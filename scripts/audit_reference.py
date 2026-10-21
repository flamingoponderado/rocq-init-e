#!/usr/bin/env python3
"""Read-only reproducible checks accompanying docs/REFERENCE-AUDIT.md.

Success means provenance/regeneration/structural checks passed, not a proof of
cross-assistant semantic equivalence. No compilation, extraction or resealing.
"""
import argparse
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path, *args):
    return subprocess.check_output(
        ['rtk', 'proxy', 'git', '-C', str(path), *args], text=True).strip()


def natural(expression, names):
    """Only natural constants/names and +, saturating -, *, ^; never eval."""
    tree = ast.parse(expression.replace('^', '**'), mode='eval')

    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            require(node.value >= 0, 'negative natural constant')
            return node.value
        if isinstance(node, ast.Name):
            return names[node.id]
        if isinstance(node, ast.BinOp):
            left, right = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return left + right
            if isinstance(node.op, ast.Sub): return max(left - right, 0)
            if isinstance(node.op, ast.Mult): return left * right
            if isinstance(node.op, ast.Pow): return left ** right
        raise ValueError('unsupported arithmetic: ' + expression)

    return visit(tree.body)


def parameters(text, rocq):
    pattern = (r'^Definition (\w+) : N := (.*?)\.$' if rocq else
               r'^def (\w+) : Nat := (.*?)$')
    values = {}
    for name, expr in re.findall(pattern, text, re.M):
        values[name] = natural(expr, values)
    require(len(values) == 20, 'parameter declaration coverage changed')
    return values


def list_body(text, marker):
    start = text.index('[', text.index(marker))
    depth = 0
    for end in range(start, len(text)):
        depth += (text[end] == '[') - (text[end] == ']')
        if depth == 0:
            return text[start:end + 1]
    raise ValueError('unterminated list: ' + marker)


def number_list(body):
    # Restricted literal grammar, independently parsed after removing n2w.
    text = re.sub(r'\(n2w\s+(0x[0-9a-fA-F]+|[0-9]+)\)', r'\1', body)
    text = re.sub(r'\bn2w\s+(0x[0-9a-fA-F]+|[0-9]+)', r'\1', text)
    require(re.fullmatch(r'[\s\[\],;0-9a-fA-Fx]+', text) is not None,
            'nonliteral numeric list')
    result = ast.literal_eval(text.replace(';', ','))
    def valid(x):
        return (type(x) is int and x >= 0) or (
            isinstance(x, list) and all(valid(y) for y in x))
    require(valid(result), 'invalid numeric list')
    return result


def audit(references):
    checks = {}
    lock = json.loads((ROOT / 'reference-lock.json').read_text())
    provenance = {}
    for path, expected in lock['dependencies'].items():
        actual = git(references / path, 'rev-parse', 'HEAD')
        require(actual == expected['commit'], 'wrong dependency commit: ' + path)
        require(not git(references / path, 'status', '--porcelain', '--untracked-files=all'),
                'dirty dependency: ' + path)
        provenance[path] = dict(expected, actual=actual)
    checks['clean_locked_dependencies'] = len(provenance)

    regeneration = []
    for name in ['import_guest', 'import_reduced_types',
                 'import_reduced_decoder', 'import_decoder']:
        spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        if name != 'import_guest':
            module.SOURCE = references / module.SOURCE.relative_to(ROOT)
        require(module.TARGET.read_text() == module.render(), name + ' regeneration differs')
        if name == 'import_reduced_types':
            declarations = list(module.declarations())
            checks['reduced_carrier_declarations'] = len(declarations)
            checks['reduced_record_fields'] = sum(len(d[2]) for d in declarations if d[0] == 'structure')
            checks['reduced_constructors'] = sum(len(d[2]) for d in declarations if d[0] == 'inductive')
        regeneration.append({'importer': name,
                             'source_sha256': digest(module.SOURCE),
                             'target': str(module.TARGET.relative_to(ROOT)),
                             'target_sha256': digest(module.TARGET)})
    checks['byte_exact_regeneration'] = regeneration

    revision = (ROOT / 'source/stateless-pancaketh/REVISION').read_text()
    for name in ['SoftwareAst.lean', 'guest-software.pp.pnk']:
        expected = re.search(r'Guest/' + re.escape(name) + r' sha256: ([0-9a-f]{64})', revision)
        require(expected is not None and
                digest(ROOT / 'source/stateless-pancaketh/Guest' / name) == expected[1],
                'software guest snapshot hash differs: ' + name)
    baseline_manifest = json.loads((ROOT / 'source/init-e-baseline/MANIFEST.json').read_text())
    require(digest(ROOT / 'source/init-e-baseline/Bookkeeping.lean') ==
            baseline_manifest['bookkeeping_sha256'], 'baseline bookkeeping snapshot differs')
    require(digest(ROOT / 'source/init-e-baseline/CompilerConfigLiteral.lean') ==
            baseline_manifest['compiler_config_sha256'], 'baseline compiler config snapshot differs')

    lean = (ROOT / 'source/stateless-pancaketh/Guest/SoftwareAst.lean').read_text()
    require(len(re.findall(r'^def ', lean, re.M)) ==
            len(re.findall(r'^def guest\w+ : (?:Decl \(BitVec 64\)|List \(Decl \(BitVec 64\)\)) :=$', lean, re.M)),
            'AST declaration header not covered by importer')
    # Current fixed AST names have an injective ASCII -> mlstring encoding.
    strings = re.findall(r'"([^"\\]*)"', lean)
    require(all(all(ord(c) < 128 for c in s) for s in strings), 'non-ASCII AST name')
    checks['ast_declarations'] = len(re.findall(r'^def ', lean, re.M))
    checks['ascii_ast_string_occurrences'] = len(strings)

    p = parameters((references / 'reference/init-e/InitE/Parameters.lean').read_text(), False)
    rocq_p = parameters((ROOT / 'theories/InitE/Parameters.v').read_text(), True)
    source_layout = {'globalsWords', 'heapEnd'}
    require({k: v for k, v in p.items() if k not in source_layout} ==
            {k: v for k, v in rocq_p.items() if k not in source_layout},
            'parameter values differ')
    require(rocq_p['globalsWords'] == len(re.findall(r'^def guestGlobal_', lean, re.M)),
            'software guest globalsWords differs')
    checks['parameter_values'] = p
    startup = number_list(list_body((ROOT / 'source/init-e-baseline/Bookkeeping.lean').read_text(), 'def startupHeaders'))
    require(startup == number_list(list_body((ROOT / 'theories/Guest/Bookkeeping.v').read_text(), 'Definition startupHeaders')),
            'startup words differ')
    checks['startup_words'] = startup

    calls = sorted(set(re.findall(r'Prog.extCall "([a-z0-9_]+)"', lean)))
    require(calls == ['halt', 'trap'], 'software guest has unexpected external calls')
    checks['software_guest_external_calls'] = calls

    # Hash the manually reviewed local semantic surface, including shared libs
    # separately pinned above; hashes identify evidence, not correctness.
    local = sorted(set(ROOT.glob('theories/Target/Reduced*.v')) |
                   set(ROOT.glob('theories/Guest/*.v')) |
                   set(ROOT.glob('theories/InitE/*.v')) |
                   {ROOT / 'theories/Target/Configuration.v'})
    return {'scope': 'provenance, regeneration and structural checks only',
            'review_base': '30ce3e13c01daa0febf115b34c70c2593f7a6dad',
            'dependencies': provenance, 'checks': checks,
            'local_sha256': {str(p.relative_to(ROOT)): digest(p) for p in local},
            'open_obligations': [
                'At review base: independent Lean holTheNone versus Rocq THE None = ARB; pending opaque-choice repair (see audit).',
                'No cross-assistant theorem for all shared evaluator/word/choice foundations.',
                'Native extracted compiler result requires kernel equality and complete certificate.']}


def corruption_checks(references):
    """Exercise rejection against isolated copies; never mutate reviewed trees."""
    global ROOT
    original_root = ROOT
    passed = []
    with tempfile.TemporaryDirectory(prefix='reference-audit-regression-') as scratch:
        try:
            ROOT = Path(scratch)
            paths = ['reference-lock.json', 'theories/Target/Configuration.v']
            paths += [str(p.relative_to(original_root))
                      for p in (original_root / 'scripts').glob('import_*.py')]
            paths += ['theories/Guest/Ast.v', 'theories/Target/ReducedTypes.v',
                      'theories/Target/ReducedDecode.v', 'theories/Target/Decode.v',
                      'theories/InitE/Parameters.v', 'theories/Guest/Bookkeeping.v',
                      'source/stateless-pancaketh/Guest/SoftwareAst.lean',
                      'source/stateless-pancaketh/Guest/guest-software.pp.pnk',
                      'source/stateless-pancaketh/REVISION',
                      'source/init-e-baseline/Bookkeeping.lean',
                      'source/init-e-baseline/CompilerConfigLiteral.lean',
                      'source/init-e-baseline/MANIFEST.json']
            for path in paths:
                target = ROOT / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(original_root / path, target)
            audit(references)
            mutations = [
                ('theories/Guest/Ast.v', lambda s: s + '\n(* drift *)\n',
                 'import_guest regeneration differs'),
                ('theories/InitE/Parameters.v',
                 lambda s: s.replace('200000000', '199999999'),
                 'parameter values differ'),
                ('source/stateless-pancaketh/Guest/SoftwareAst.lean',
                 lambda s: s.replace('Prog.extCall "trap"', 'Prog.extCall "sha256f"'),
                 'import_guest regeneration differs')]
            for path, mutate, expected in mutations:
                target = ROOT / path
                original = target.read_text()
                target.write_text(mutate(original))
                try:
                    audit(references)
                except ValueError as exc:
                    require(str(exc) == expected, 'unexpected rejection: ' + str(exc))
                    passed.append(expected)
                else:
                    raise ValueError('corruption accepted: ' + path)
                finally:
                    target.write_text(original)
            require(natural('3 - 5', {}) == 0, 'natural subtraction mismatch')
            try:
                natural('__import__("os")', {})
            except ValueError:
                passed.append('restricted arithmetic rejects calls')
            else:
                raise ValueError('arithmetic accepted executable expression')
        finally:
            ROOT = original_root
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--references-root', type=Path, default=ROOT,
                        help='checkout containing clean pinned reference/ and vendor/ trees (read-only)')
    parser.add_argument('--self-test', action='store_true',
                        help='also reject deliberate corruption in temporary copies')
    args = parser.parse_args()
    try:
        references = args.references_root.resolve()
        result = audit(references)
        if args.self_test:
            result['corruption_rejections'] = corruption_checks(references)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        print('reference audit checks failed: ' + str(exc), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
