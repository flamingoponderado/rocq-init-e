# Submission protocol and operator replay

The isolated verifier is implemented. The previous baseline passed the coherent
library build, recursive kernel replay, and positive sealed verifier acceptance
on 2026-10-12. The guest with software precompiles in this PR requires a new
full build and verifier run. Commands below reproduce the current checkout; the
previous accepted result and kernel context are retained in
baseline-positive-verifier-result.json and
baseline-positive-verifier-kernel.log.
See [PORT-STATUS.md](PORT-STATUS.md) and
[FINAL-PORT-REVIEW.md](FINAL-PORT-REVIEW.md) for dated evidence and open obligations.
Do not restart the coordinator's active rebuild or verifier pipeline.

## Participant package and exact certificate

A package directory contains `rom.bin`, `claim.json`, `Solution.v` and optional
Rocq helper sources. Compiled/binary helpers, symlinks and unsupported paths are
rejected. Use ASCII identifier directory names and `.v` source filenames.
`claim.json` contains exactly `{"K":"infinity"}` or `{"K":123}` with a
nonnegative integer K. Duplicate keys, booleans, floats and other fields are
rejected; JSON is limited to 1 MiB. The ROM bound is 1..128 MiB of arbitrary
bytes, the original code admission bound rather than an input-blob restriction.

The verifier generates `SubmissionLiterals.Values` from the captured ROM and
claim. `Solution.v` must export a `submission : Submission` and a proved
`certificate` of this exact type (names refer to SubmissionModel and Challenge):

```text
Certificate
 (Build_Submission submittedCode claimedScore
  (anchorPc submission) (names submission) (first submission) (extra submission))
 claimedScore
```

The expected proposition is resolved in precompiled
[VerificationCore.v](../theories/InitE/VerificationCore.v) before participant
sources are loaded. Only anchor/names/first/extra metadata comes from the exported
submission; the checker rebuilds its code and K from protected literals. A proof
of `True`, a certificate for another ROM, or a different score cannot pass
conversion. The metadata must satisfy all original admission conditions.
Axioms or admitted proofs cannot substitute for the certificate: the final kernel
policy rejects assumptions outside its five foundation axioms.

The fixed challenge quantifies over every input with declared gas <=200,000,000,
every terminating source result and covered outcome. No additional input-size,
installation or native-state premise is permitted. `infinity` requires an actual
finite evaluator Halt matching the original observations, not a timeout or
vacuous behaviour claim. Arbitrary admitted ROM uses the original reduced target;
it is not restricted to compiler-generated instruction paths.

## Fresh reviewed checkout and toolchain

Use a Linux host with Python 3, Git, RTK, opam, a C toolchain/GMP development
support, and Bubblewrap with permitted user/PID/network namespaces. The observed
opam versions are:

| Package | Version |
| --- | --- |
| ocaml-base-compiler / OCaml | 5.2.1 |
| dune | 3.24.2 |
| rocq-core, rocq-runtime | 9.3.0 |
| rocq-prover | meta.1 |
| rocq-stdlib | 9.2.0 |
| zarith | 1.14 |

The version of the Stdlib package is distinct from the Rocq prover version.
For a new switch, the following selects those packages; do not replace an
operator's active environment while a verification job is running:

```sh
rtk proxy opam switch create rocq-init-e ocaml-base-compiler.5.2.1
rtk proxy opam install --switch=rocq-init-e dune.3.24.2 rocq-core.9.3.0 \
  rocq-runtime.9.3.0 rocq-prover.meta.1 rocq-stdlib.9.2.0 zarith.1.14
rtk proxy opam exec --switch=rocq-init-e -- rocq --version
rtk proxy opam exec --switch=rocq-init-e -- ocamlc -version
rtk proxy opam exec --switch=rocq-init-e -- dune --version
```

Clone the repository in an operator-owned directory. Replace
`REVIEWED_RELEASE_COMMIT` with the final reviewed commit, which must include
CompilationCertificate, BaselineCertificate and `scripts/make_baseline_submission.py`.
The documentation task's earlier review base alone does not contain those files.
Select pinned submodules after checking out that commit:

```sh
rtk proxy git clone https://github.com/flamingoponderado/rocq-init-e.git
rtk proxy git -C rocq-init-e checkout REVIEWED_RELEASE_COMMIT
rtk proxy git -C rocq-init-e submodule update --init --recursive
```

Run the remaining commands from that checkout. Reference and Galette commits
must match [reference-lock.json](../reference-lock.json); treat their trees as
read-only. The existing reference audit checks every pin and clean working tree,
regenerates guest/reduced-carrier/decoder files in memory, and checks constants:

```sh
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/audit_reference.py --self-test
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/import_baseline.py --check
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/import_baseline_metadata.py --check
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s verifier -p 'test_*.py' -v
```

These structural checks and unit tests are not full semantic fidelity proofs or
positive CLI acceptance. The full original compilation theorem can be expensive
on a clean build. Schedule one heavy build/kernel/replay at a time; do not delete
or mutate an active build tree, restart its compiler or reseal during a run.

## Build, kernel-check and seal

From the fresh reviewed checkout, using the switch above. Run each command only
after the preceding one exits with status 0; stop on any failure before sealing:

```sh
rtk proxy opam exec --switch=rocq-init-e -- dune build -j 1
rtk proxy opam exec --switch=rocq-init-e -- rocq check -bytecode-compiler yes -silent -o \
  -Q _build/default/galette-theories Galette \
  -Q _build/default/theories InitE InitE.InitE.VerificationCore
rtk proxy opam exec --switch=rocq-init-e -- rocq check -bytecode-compiler yes -silent -o \
  -Q _build/default/galette-theories Galette \
  -Q _build/default/theories InitE InitE.Baseline.BaselineCertificate
rtk proxy opam exec --switch=rocq-init-e -- python3 scripts/seal_verifier.py
```

Retain the complete build/kernel logs and inspect every context section before
sealing. The whitelist in [policy.py](../verifier/policy.py) is exactly classic,
constructive indefinite description, dependent functional extensionality,
propositional extensionality and proof irrelevance from `Stdlib.Logic`.
A subset, including no assumptions, is allowed. Type-in-type, unsafe fixpoints,
assumed positivity, unexpected/duplicate context sections and extra axioms are
rejected by the verifier. Do not change policy to accommodate a failing proof.

The native proof chain is actual bootstrap reachability -> exact native/header/
bitmap/source-memory installation -> full `pan_installed` -> Galette compiler
correctness with resource relaxation removed by 538 < 2,097,104 -> finite native
Halt by TargetTotality -> initial-state matching execution by bootstrap clock
shift. Concrete compiler-output/metadata equality closes the intermediate inputs.
The final certificate must have type `Certificate baselineSubmission infinity`
without compilation, installation, native-state or source nonFail hypotheses.

`seal_verifier.py` hashes source/object inventory, build/policy files and the
Rocq launcher; it only checks that the verifier interface source/object exists.
It does not itself prove freshness or run the kernel checker. Seal only after a
coherent, reviewed, recursively checked build. Verification never reseals;
changes, additions or resealing during a run invalidate it. A launcher hash does
not attest the complete external worker/runtime/plugin/Stdlib/OS closure.
Keep the checkout, seal, installation, `/usr`, system libraries and entire Rocq
prefix inaccessible to participant writes throughout every run. Read-only
sandbox mounts do not authenticate an operator-controlled toolchain.

## Software-guest baseline package and CLI gates

The final integrated `scripts/make_baseline_submission.py` reconstructs the
software-guest ROM from clean pinned Prefix000..001, Bytes000..239 and Suffix000..010
Lean literals by default. It needs no private extracted-proposal directory.
The package has 1,028,080 bytes, score `infinity`, and ROM SHA256
`44b6a6b828293a54cf2e8698a6a0af6a0d08b4ea825f6504547996c31969d04b`.
It includes a proof binding the protected generated bytes to Artifacts.code;
package creation itself is not acceptance. Optional `--rom /path/to/rom.bin`
uses an existing ROM only after exact pinned size/digest validation.

All package/replay output paths below must be fresh; retain existing logs
rather than reuse or overwrite them. Use an operator-owned output parent.

```sh
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/make_baseline_submission.py \
  --output .artifacts/baseline-package-release
rtk proxy opam exec --switch=rocq-init-e -- python3 scripts/test_verifier_cli.py \
  --output .artifacts/negative-replay-release
rtk proxy opam exec --switch=rocq-init-e -- python3 verifier/verify.py \
  .artifacts/baseline-package-release --output .artifacts/baseline-replay-release \
  --timeout 21600
```

The existing real negative suite requires wrong-statement, wrong-ROM and
wrong-score cases to fail module comparison, and the exact-shaped extra-axiom
case to fail kernel policy. Reaching the wrong failure stage is not a passing
negative regression. For other participants, replace the baseline package path
with their package directory and use another fresh replay output.

Only a successful complete run prints `VERIFIED` and writes `result.json`.
For the software-guest baseline require `verified: true`, `rom_bytes: 1028080`, the ROM
SHA256 above, `score_literal: "infinity"`, `kernel_exit: 0`, a permitted axiom set
and the final operator seal digest. Retain candidate compilation/dependency logs,
`comparison.log`, the entire `kernel.log`, generated literals and `result.json`.
Standalone compilation success, package generation or an empty log does not
constitute positive verification. At this checkpoint that positive run is pending.

## Isolation and original-fidelity limits

The verifier reads regular-file descriptors without following symlinks in any
path component and detects concurrent writes. It rechecks copied sources,
captures ROM/claim bytes and snapshots the exact hashed trusted source/objects.
Every stage runs in a private directory under `/tmp`; the main `_build` is never
mounted or written by a stage. Logs are published to the requested output after
sandbox processes exit, including stage failures.

Bubblewrap clears the environment and unshares namespaces, including network
and PID. Only the toolchain/system paths, trusted snapshots, protected literals
and stage-specific package/checker files are mounted. Candidate compilation can
write its own directory; literals and trusted libraries remain read-only. Module
comparison reads candidate objects read-only and the recursive kernel stage
reads all its inputs read-only. Plugins, extraction, notation/export substitution,
file redirection, Load and load-path directives are unsupported, including
wrapped commands. Source guards support the sandbox and kernel gates; they do
not replace those stages or constitute a general Rocq grammar proof. The default
timeout is 10,800 seconds per stage with a 112 GiB address-space ceiling.
The previous baseline replay used `--timeout 21600`: its first run reached the
three-hour timeout without a proof failure, and the unchanged sealed retry passed.
The software-guest baseline replay is pending.

Original init-e is the authority, with exact pins and definition comparisons in
[REFERENCE-AUDIT.md](REFERENCE-AUDIT.md) and
[EVALUATOR-AUDIT.md](EVALUATOR-AUDIT.md). Formal Lean-to-Rocq decoder/step and
shared evaluator/FFI/word/accelerator/observation correspondence remains open.
The compatible interpretation of opaque failed-THE/arbitrary choices and
common-constructor encoder byte equality require explicit treatment. Internal
Rocq reduced-to-full compiler proofs and exact original byte hashes do not
establish those cross-assistant theorems. Keep these fidelity limits visible even
after the baseline CLI passes.
