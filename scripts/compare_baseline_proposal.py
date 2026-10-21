#!/usr/bin/env python3
"""Compare an untrusted native proposal with pinned software guest Lean literals.

This is an artifact comparison, never a kernel compilation certificate.
Only the pinned decimal/hex list syntax is accepted.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def literal(path, name, width):
    text = path.read_text()
    pattern = (r"import Std\s+namespace InitECandidate\s+def " + re.escape(name)
               + r" : List \(BitVec " + str(width * 8)
               + r"\) := \[([\s,0-9a-fx]+)\]\s+end InitECandidate\s*")
    match = re.fullmatch(pattern, text)
    if not match:
        raise ValueError("unexpected literal syntax: " + str(path))
    tokens = [x.strip() for x in match[1].split(",") if x.strip()]
    if not all(re.fullmatch(r"0x[0-9a-f]+|[0-9]+", x) for x in tokens):
        raise ValueError("invalid numeric token: " + str(path))
    values = [int(x, 16 if x.startswith("0x") else 10) for x in tokens]
    return b"".join(n.to_bytes(width, "little") for n in values)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path,
                        help="create a fresh directory with original full ROM and bitmap bytes")
    args = parser.parse_args()
    root = ROOT / "source/init-e-baseline/InitECandidate"
    def chunks(prefix):
        paths = sorted(root.glob(prefix.title() + "[0-9][0-9][0-9].lean"))
        if not paths or [int(path.stem[-3:]) for path in paths] != list(range(len(paths))):
            raise ValueError("noncontiguous " + prefix + " chunks")
        return b"".join(literal(path, prefix + path.stem[-3:], 1) for path in paths)
    native = chunks("bytes")
    bitmaps = literal(root / "Bitmaps.lean", "bitmaps", 8)
    prefix = chunks("prefix")
    suffix = chunks("suffix")
    rom = prefix + native + suffix
    result = {"scope": "byte comparison only; no kernel compilation certificate",
              "native_same_as_original": native == (args.proposal / "native.bin").read_bytes(),
              "bitmap_same_as_original": bitmaps == (args.proposal / "bitmaps.bin").read_bytes(),
              "native_bytes": len(native), "bitmap_words": len(bitmaps) // 8,
              "prefix_bytes": len(prefix), "suffix_bytes": len(suffix), "rom_bytes": len(rom),
              "native_sha256": hashlib.sha256(native).hexdigest(),
              "bitmap_sha256": hashlib.sha256(bitmaps).hexdigest(),
              "rom_sha256": hashlib.sha256(rom).hexdigest()}
    if not result["native_same_as_original"] or not result["bitmap_same_as_original"]:
        print(json.dumps(result, indent=2)); return 1
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=False)
        (args.output_dir / "rom.bin").write_bytes(rom)
        (args.output_dir / "bitmaps.bin").write_bytes(bitmaps)
        (args.output_dir / "comparison.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
