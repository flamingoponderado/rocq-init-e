#!/usr/bin/env python3
"""Import baseline byte and bitmap literals, not Lean proofs.

Generated values are proposals until the Rocq compilation equality is proved.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
from compare_baseline_proposal import literal
ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'source/init-e-baseline/MANIFEST.json'
SOURCE = ROOT / 'source/init-e-baseline/InitECandidate'
TARGET = ROOT / "theories/Baseline/Artifacts.v"


def chunk_paths(source, prefix):
    paths = sorted(source.glob(prefix.title() + '[0-9][0-9][0-9].lean'))
    indices = [int(re.fullmatch(prefix.title() + r'([0-9]{3})\.lean', p.name)[1])
               for p in paths]
    if not paths or indices != list(range(len(paths))):
        raise ValueError('missing or noncontiguous ' + prefix + ' chunks')
    return paths


def render(source_override=None):
    source = source_override or SOURCE
    manifest = json.loads(MANIFEST.read_text())
    expected_files = manifest['files_sha256']
    actual_files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in source.glob('*.lean')}
    if actual_files != expected_files:
        raise ValueError('baseline source literal hashes differ')
    out = ["(** Software guest baseline literals from init-e " + manifest['source_commit'] + ".",
           "    Imported data only; compiler equality and certificate are separate gates. *)",
           "From Galette Require Import Base.",
           "From Galette.HOL.src.n_bit Require Import words.",
           "Open Scope N_scope."]
    component_bytes = {}
    for prefix, public in [("prefix", "bootPrefix"),
                           ("bytes", "nativeCode"),
                           ("suffix", "suffix")]:
        chunks = []
        component = bytearray()
        for i, path in enumerate(chunk_paths(source, prefix)):
            data = literal(path,
                           prefix + f"{i:03}", 1)
            component.extend(data)
            for j in range(0, len(data), 1024):
                name = prefix + f"_{i:03}_{j//1024}"
                chunks.append(name)
                out.append("Definition " + name + " : list (word 8) := [" +
                           ";".join("n2w " + str(b) for b in data[j:j+1024]) + "].")
        out.append("Definition " + public + " : list (word 8) := concat [" +
                   ";".join(chunks) + "].")
        component_bytes[prefix] = bytes(component)
        expected = manifest[{'prefix': 'prefix_sha256', 'bytes': 'native_sha256',
                             'suffix': 'suffix_sha256'}[prefix]]
        if hashlib.sha256(component).hexdigest() != expected:
            raise ValueError(prefix + ' byte hash differs')
    if sum(map(len, component_bytes.values())) != manifest['rom_bytes']:
        raise ValueError('ROM byte length differs')
    rom = component_bytes['prefix'] + component_bytes['bytes'] + component_bytes['suffix']
    if hashlib.sha256(rom).hexdigest() != manifest['rom_sha256']:
        raise ValueError('ROM byte hash differs')
    data = literal(source / "Bitmaps.lean", "bitmaps", 8)
    if len(data) // 8 != manifest['bitmaps_words'] or \
       hashlib.sha256(data).hexdigest() != manifest['bitmaps_sha256']:
        raise ValueError('bitmap literal hash differs')
    values = [int.from_bytes(data[i:i+8], "little") for i in range(0, len(data), 8)]
    out.append("Definition bitmaps : list (word 64) := [" +
               ";".join("n2w " + str(n) for n in values) + "].")
    out.append("Definition code : list (word 8) := bootPrefix ++ nativeCode ++ suffix.")
    return "\n".join(out) + "\n"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check", action="store_true")
    p.add_argument("--source", type=Path,
                   help="alternate directory of the pinned Lean InitECandidate literals")
    args = p.parse_args()
    content = render(args.source)
    if args.check:
        if TARGET.read_text() != content:
            raise SystemExit("baseline literal regeneration differs")
    else:
        TARGET.parent.mkdir(parents=True, exist_ok=True)
        TARGET.write_text(content)


if __name__ == "__main__":
    main()
