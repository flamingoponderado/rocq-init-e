#!/usr/bin/env python3
"""Package the pinned software-guest baseline for the isolated verifier."""
import argparse
import hashlib
import json
from pathlib import Path
from compare_baseline_proposal import literal

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "source/init-e-baseline/MANIFEST.json"
SOURCE = ROOT / "source/init-e-baseline/InitECandidate"
SOLUTION = r"""From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.InitE Require Import NatE SubmissionModel Challenge.
From InitE.Baseline Require Import Artifacts Submission BitmapImageFacts BaselineCertificate.
From SubmissionLiterals Require Import Values.
Open Scope N_scope.
Definition submission : Submission := baselineSubmission.
Lemma submitted_code_binding : submittedCode = Artifacts.code.
Proof. apply word_list_numeric_ext; vm_compute; reflexivity. Qed.
Definition certificate : Certificate
 (Build_Submission submittedCode claimedScore (anchorPc submission)
  (names submission) (first submission) (extra submission)) claimedScore.
Proof. rewrite submitted_code_binding; exact baseline_certificate. Qed.
"""

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rom", type=Path, help="optional existing ROM; default reconstructs pinned software guest literals")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    expected_files = manifest["files_sha256"]
    actual_files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in SOURCE.glob("*.lean")}
    if actual_files != expected_files:
        raise SystemExit("pinned software guest literal hashes differ")
    if args.rom is None:
        chunks = []
        for prefix in ("prefix", "bytes", "suffix"):
            paths = sorted(SOURCE.glob(prefix.title() + "[0-9][0-9][0-9].lean"))
            if not paths or [p.name for p in paths] != [prefix.title() + f"{i:03}.lean"
                                                        for i in range(len(paths))]:
                raise SystemExit("missing or noncontiguous " + prefix + " literals")
            chunks.extend(literal(path, prefix + f"{i:03}", 1)
                          for i, path in enumerate(paths))
        data = b"".join(chunks)
    else:
        if args.rom.is_symlink() or not args.rom.is_file():
            raise SystemExit("ROM must be a regular file")
        if args.rom.stat().st_size != manifest["rom_bytes"]:
            raise SystemExit("ROM differs from the pinned software guest baseline")
        data = args.rom.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if len(data) != manifest["rom_bytes"] or digest != manifest["rom_sha256"]:
        raise SystemExit("ROM differs from the pinned software guest baseline")
    if args.output.exists():
        raise SystemExit("output directory already exists")
    args.output.mkdir(parents=True)
    (args.output / "rom.bin").write_bytes(data)
    (args.output / "claim.json").write_text(json.dumps({"K": "infinity"}) + "\n")
    (args.output / "Solution.v").write_text(SOLUTION)
    print(json.dumps({"package": str(args.output), "rom_bytes": len(data), "rom_sha256": digest,
                      "score": "infinity", "verification_required": True}))

if __name__ == "__main__":
    main()
