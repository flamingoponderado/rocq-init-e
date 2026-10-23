#!/usr/bin/env python3
"""Compile checkpoints sequentially with per-file and total time limits.

Uses existing Dune-built dependencies. Run inside the project's opam environment.
Stops on the first failure/timeout and leaves successful .vo files reusable.
"""
import argparse
import hashlib
import json
import os
import signal
import re
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--timeout', type=float, default=60)
    p.add_argument('--budget', type=float, default=180)
    p.add_argument('--keep-going', action='store_true',
                   help='continue independent files after a failure and skip its dependents')
    p.add_argument('files', nargs='*')
    args = p.parse_args()
    if args.timeout <= 0 or args.budget <= 0:
        p.error('timeouts must be positive')
    # Visit imported checkpoint files before their consumers, so each timeout
    # measures one compilation unit rather than its entire unfinished ancestry.
    directory = ROOT / 'theories/Compilation'
    sources = {path.stem: path for path in directory.glob('*.v')}
    def imports(path):
        names = []
        for group in re.findall(r'From InitE\.Compilation Require (?:Import |Export )?([^.]*)\.', path.read_text()):
            names.extend(name for name in group.split() if name in sources)
        return [sources[name] for name in names]
    requested = ([ROOT / f for f in args.files] if args.files else
                 [ROOT / 'theories/Baseline/CompilationCertificate.v'])
    paths, visiting, visited = [], set(), set()
    def visit(path):
        if path in visited:
            return
        if path in visiting:
            p.error('Cyclic checkpoint imports: ' + str(path))
        visiting.add(path)
        if path.exists():
            for dependency in imports(path):
                visit(dependency)
        visiting.remove(path)
        visited.add(path)
        paths.append(path)
    for path in requested:
        visit(path)
    missing = [str(path.relative_to(ROOT)) for path in paths if not path.exists()]
    if missing:
        p.error('Missing checkpoint sources; run generate_compilation_checkpoints.py first: ' + ', '.join(missing[:3]))
    logs = ROOT / '_build/checkpoints'
    logs.mkdir(parents=True, exist_ok=True)
    built = [f for f in (ROOT / '_build/default').rglob('*.vo')
             if 'theories/Compilation' not in str(f)]
    dependency_time = max((f.stat().st_mtime for f in built), default=0)
    start = time.monotonic()
    report = logs / 'timings.json'
    results = json.loads(report.read_text()) if report.exists() else []
    run_results = []
    successful = {r['file']: r for r in results if r['status'] == 0}
    failed = set()
    for path in paths:
        if any(dependency in failed for dependency in imports(path)):
            failed.add(path)
            continue
        production = path.is_relative_to(ROOT / 'theories')
        # Invalidate against every local imported checkpoint, including split phases.
        dependency_files = []
        for names in re.findall(r'From InitE\.Compilation Require (?:Import |Export )?([^.]*)\.', path.read_text()):
            for name in names.split():
                for directory in ['_build/default/theories/Compilation']:
                    dep = ROOT / directory / (name + '.vo')
                    if dep.exists():
                        dependency_files.append(dep)
        newest = max([path.stat().st_mtime, dependency_time] +
                     [f.stat().st_mtime for f in dependency_files])
        vo = ((ROOT / '_build/default' / path.relative_to(ROOT)).with_suffix('.vo')
              if production else path.with_suffix('.vo'))
        key = str(path.relative_to(ROOT))
        signature = hashlib.sha256(path.read_bytes())
        signature.update(str(dependency_time).encode())
        for dep in dependency_files:
            signature.update(f'{dep}:{dep.stat().st_mtime_ns}:{dep.stat().st_size}'.encode())
        fingerprint = signature.hexdigest()
        if vo.exists() and (vo.stat().st_mtime >= newest or
                            successful.get(key, {}).get('fingerprint') == fingerprint):
            continue
        remaining = args.budget - (time.monotonic() - start)
        if remaining <= 0:
            print('Total time budget reached; rerun to resume.', flush=True)
            return 2
        command = ['rocq', 'compile', '-time',
                   '-Q', '_build/default/galette-theories', 'Galette',
                   '-Q', '_build/default/theories', 'InitE',
                   str(path)]
        if production:
            command = ['dune', 'build', '-j', '1', str(path.relative_to(ROOT).with_suffix('.vo'))]
        before = time.monotonic()
        log = logs / (path.stem + '.log')
        print(f'Checking {path.stem}', flush=True)
        with log.open('w') as out:
            with subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                  start_new_session=True) as proc:
                try:
                    status = proc.wait(timeout=min(args.timeout, remaining))
                except subprocess.TimeoutExpired:
                    # Dune may have spawned Rocq. Stop the entire job, including
                    # children that ignore the first termination signal.
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        proc.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        pass
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    proc.wait()
                    status = 'timeout'
        seconds = round(time.monotonic() - before, 3)
        entry = {'file': key, 'seconds': seconds, 'status': status,
                 'finished_at': time.time(), 'fingerprint': fingerprint}
        results.append(entry)
        run_results.append(entry)
        report.write_text(json.dumps(results, indent=2) + '\n')
        print(f'  {status}: {seconds}s ({log.relative_to(ROOT)})', flush=True)
        if status != 0:
            print(log.read_text()[-3000:], flush=True)
            failed.add(path)
            if not args.keep_going:
                return 1
    recent = run_results
    slowest = sorted((r for r in recent if r['status'] == 0),
                     key=lambda r: r['seconds'], reverse=True)[:10]
    print('Slowest completed files:', flush=True)
    for item in slowest:
        print(f"  {item['seconds']:.3f}s {item['file']}", flush=True)
    if failed:
        print(f'{len(failed)} failed or dependency-blocked files.', flush=True)
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
