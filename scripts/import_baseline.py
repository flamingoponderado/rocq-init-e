#!/usr/bin/env python3
"""Import only the original baseline byte and bitmap literals, not Lean proofs.

Generated values are proposals until the Rocq compilation equality is proved.
"""
import argparse
import subprocess
from pathlib import Path
from compare_baseline_proposal import literal
ROOT = Path(__file__).resolve().parents[1]
PIN = "b3831bc501713e27b9f6974a5eb3cd0b1ca0d2c2"
TARGET = ROOT / "theories/Baseline/Artifacts.v"


def render():
    ref = ROOT / "reference/init-e"
    actual = subprocess.check_output(["rtk", "proxy", "git", "-C", str(ref),
                                      "rev-parse", "HEAD"], text=True).strip()
    if actual != PIN:
        raise ValueError("original init-e pin mismatch")
    dirty = subprocess.check_output(["rtk", "proxy", "git", "-C", str(ref),
                                     "status", "--porcelain", "--untracked-files=all"], text=True)
    if dirty.strip():
        raise ValueError("original init-e reference is dirty")
    source = ref / "submission/InitECandidate"
    out = ["(** Original init-e baseline literals at " + PIN + ".",
           "    Imported data only; compiler equality and certificate are separate gates. *)",
           "From Galette Require Import Base.",
           "From Galette.HOL.src.n_bit Require Import words.",
           "Open Scope N_scope."]
    for prefix, count, public in [("prefix", 2, "bootPrefix"),
                                  ("bytes", 221, "nativeCode"),
                                  ("suffix", 11, "suffix")]:
        chunks = []
        for i in range(count):
            data = literal(source / (prefix.title() + f"{i:03}.lean"),
                           prefix + f"{i:03}", 1)
            for j in range(0, len(data), 1024):
                name = prefix + f"_{i:03}_{j//1024}"
                chunks.append(name)
                out.append("Definition " + name + " : list (word 8) := [" +
                           ";".join("n2w " + str(b) for b in data[j:j+1024]) + "].")
        out.append("Definition " + public + " : list (word 8) := concat [" +
                   ";".join(chunks) + "].")
    data = literal(source / "Bitmaps.lean", "bitmaps", 8)
    values = [int.from_bytes(data[i:i+8], "little") for i in range(0, len(data), 8)]
    out.append("Definition bitmaps : list (word 64) := [" +
               ";".join("n2w " + str(n) for n in values) + "].")
    out.append("Definition code : list (word 8) := bootPrefix ++ nativeCode ++ suffix.")
    return "\n".join(out) + "\n"


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    content = render()
    if args.check:
        if TARGET.read_text() != content:
            raise SystemExit("baseline literal regeneration differs")
    else:
        TARGET.parent.mkdir(parents=True, exist_ok=True)
        TARGET.write_text(content)


if __name__ == "__main__":
    main()
