#!/usr/bin/env python3
"""Package the exact original baseline for the isolated literal-bound verifier."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from compare_baseline_proposal import literal

ROOT = Path(__file__).resolve().parents[1]
REFERENCE_PIN = "b3831bc501713e27b9f6974a5eb3cd0b1ca0d2c2"
ROM_SHA256 = "22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc"
ROM_BYTES = 950344
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
    parser.add_argument("--rom", type=Path, help="optional existing ROM; default reconstructs pinned original literals")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    reference = ROOT / "reference/init-e"
    pin = subprocess.check_output(["git", "-C", str(reference), "rev-parse", "HEAD"], text=True).strip()
    if pin != REFERENCE_PIN:
        raise SystemExit("original init-e reference pin changed")
    dirty = subprocess.check_output(["git", "-C", str(reference), "status", "--porcelain",
                                     "--untracked-files=all"], text=True)
    if dirty.strip():
        raise SystemExit("original init-e reference is dirty")
    if args.rom is None:
        source = reference / "submission/InitECandidate"
        data = b"".join(literal(source / (prefix.title() + f"{i:03}.lean"),
                                prefix + f"{i:03}", 1)
                        for prefix, count in [("prefix", 2), ("bytes", 221), ("suffix", 11)]
                        for i in range(count))
    else:
        if args.rom.is_symlink() or not args.rom.is_file():
            raise SystemExit("ROM must be a regular file")
        if args.rom.stat().st_size != ROM_BYTES:
            raise SystemExit("ROM differs from the pinned original baseline")
        data = args.rom.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if len(data) != ROM_BYTES or digest != ROM_SHA256:
        raise SystemExit("ROM differs from the pinned original baseline")
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
