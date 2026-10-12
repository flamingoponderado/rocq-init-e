# Final port review at 7ed2a4d

Review base: `7ed2a4dde65c5e1eeb169b6925e3fb471f5a5c44`.
Reviewer: `rocq-verifier`; branch: `agent/final-port-review`.
Date: 2026-10-12. Scope: read-only proof, reference and verifier review;
this new document is the only tracked change. No build, compiler evaluation,
reseal, package generation, trusted-code edit or live-job action was performed.

**This is not a completed-port or positive-verifier sign-off.** Full native
installation and the compiler correctness bridge are proved at the assigned
checkpoint. During this review the coordinator reported the actual literal
compilation and whole-ROM binding passing, and prepared the unconditional
certificate sources. The final coherent library rebuild, recursive kernel
replay, fresh seal and positive verifier run remain gates. Formal correspondence
with the original Lean semantics also remains open.
A coherent build or matching extracted hashes closes none of those gates by
itself. No new differing semantic equation or participant false-acceptance
exploit was established by this review.

## Authority and fresh evidence

Original init-e and its pinned dependencies are the authority; HOL4 annotations
and Galette's full RISC-V model are implementation/proof aids. All four inspected
reference/dependency working trees matched the lock and were clean, including
untracked files. They were read from the coordinator checkout because the
worker checkout's reference submodules are not populated.

| Dependency | Commit recorded and observed |
| --- | --- |
| Original init-e | `b3831bc501713e27b9f6974a5eb3cd0b1ca0d2c2` |
| Flapjack | `034bb5a1ed0b757082768d5406206bd2f8e31b7c` |
| riscv-zkvm | `afcbc45e1c74c2d296e032b5606dd977a304e8ad` |
| Galette | `6eab85e03c934eae714ecf5eb02061b55f2843c1` |

See [reference-lock.json](../reference-lock.json),
[REFERENCE-AUDIT.md](REFERENCE-AUDIT.md) and
[EVALUATOR-AUDIT.md](EVALUATOR-AUDIT.md). Their older open compiler/bootstrap
notes are superseded by the committed proofs described below; their formal
cross-assistant limits are not superseded.

Fresh checks in this review:

- `audit_reference.py --self-test` passed: four clean pins; byte-exact guest,
  reduced-carrier and both decoder regeneration; all 20 parameters; startup
  words; 18 accelerator names; numeric tables/moduli; four corruption rejections.
- Original baseline `Artifacts.v` regenerated exactly in memory using the
  pinned importer's `render()`. `Metadata.v` regenerated exactly from the pinned
  `CompilerConfigLiteral.lean` SHA256. Neither target file was rewritten.
- Native proposal bytes, bitmap bytes and the original full-ROM proposal were
  compared again with the original literal lists; every byte matched.
- All 18 existing verifier unit tests passed with bytecode-cache writes disabled.
  These include mocked stage execution and do not constitute a fresh positive
  CLI/kernel replay. No new tests were added.
- A command-pattern scan found no line-start `Admitted.`, `Axiom`,
  `Admit Obligations.` or `Abort.` in local theories or pinned Galette theories.
  This textual check supplements, rather than replaces, kernel context audits.
- Observed versions: Rocq 9.3.0, compiled with OCaml 5.2.1; `ocamlc` 5.2.1;
  Dune 3.24.2, matching the recorded toolchain.

| Literal | Size | SHA256 |
| --- | --- | --- |
| Native bytes | 904,196 bytes | `21e4ad09c0b75c4e7d79ea8945cca480edad6b34410099ffff8760a08158c34e` |
| Bitmaps | 4,614 little-endian 64-bit words | `1ff90e1caf1c69e47f3b9ece79a99e74884e9511f14e822bbc6f090bca020277` |
| Original full ROM | 950,344 bytes | `22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc` |

The metadata source SHA256 is
`caa50933d9d7ef7200e5785b1b371e527e833f836263b759e8c9572d2330020d`.
These provenance/regeneration/hash checks do not prove that the compiler returns
these values. `NativeCompilation.direct_compilation_exact` is a symbolic
compilation-form equality; counts, extraction and literal agreement are not the
concrete compiler-output equality. That separate equality completed in the coordinator's standalone job during this
review, as recorded below.

## Exact challenge and arbitrary submissions

Compared original `InitE/Challenge.lean` and `InitE/SubmissionModel.lean` with
[Challenge.v](../theories/InitE/Challenge.v),
[SubmissionModel.v](../theories/InitE/SubmissionModel.v),
[SourceSemantics.v](../theories/InitE/SourceSemantics.v) and
[Observations.v](../theories/InitE/Observations.v):

| Required property | Reviewed implementation |
| --- | --- |
| Participant authority | Only ROM, score, anchor, names, first MMIO index and extra MMIO metadata; fixed source, oracle, target and evaluator remain outside participant fields. |
| Inputs | Every `InputBlob`; only the original declared-gas bound of 200,000,000 appears in `Certificate.correct`. No input-size, installed-state or native-only input premise is added. |
| Admission | All 16 original admission fields remain, including strict ROM/anchor bounds, dispatch exclusions, name boundary, MMIO register/exit checks and layout bound. Baseline admission is proved unconditionally. |
| Initialization | Shared input/output mapping has priority; ROM elsewhere; ordinary RAM zero; PC at the original bootstrap, zero GPRs, VM0/MPRV3/ArchBase2, no pending fetch and explicit `NoException`. |
| Source result | Quantifies over terminating source outcomes/events and the original covered-outcome predicate; failure/divergence are not substituted for source termination. |
| Target result | An actual finite evaluator result `Halt`, with original output matching. Infinity permits an input-dependent finite witness, never a timeout or divergence witness. |
| Observations | Accepted source requires accepted target and equality at every one of 65,536 output offsets; other covered results require covered, nonaccepted target. Resource-limit outcome is uncovered; trap configuration exceptions remain 1/6/7 bytes. |

The public target uses [Configuration.riscvTarget](../theories/Target/Configuration.v)
and the original reduced carrier and directly ported decoder/step. Arbitrary
admitted ROM is not replaced by the baseline, predecoded by the verifier, or
restricted by a successful-compiler-step premise. Unsupported instructions keep
the original reduced dispatch/fault path. Public FFI names remain byte-valued
`mlstring`, not a host UTF-8 normalization of arbitrary names.

The full-model embedding is a proof device, not a replacement challenge state.
`reduced_decoder_embedding` is all-word internal Rocq decoder agreement;
`reduced_next_embedding` is internal step agreement under original `riscvOk`.
`reduced_riscv_encoder_correct` covers the actual reduced target. FP stand-ins
are excluded by its zero-FP-register admissibility proof. None of these states
an all-state theorem relating Rocq execution to original Lean execution.

## Proven certificate chain and remaining computational antecedents

[PanInstallation.v](../theories/Baseline/PanInstallation.v) proves
`baseline_pan_installed` for every actual target state related to
`bootstrapEndpoint`, and its source-initial-state version for every input.
The fixed instance is nativeCode/620-byte code buffer/bitmaps/data_sp0,
`Some baselineNames`, registers `(11,13)`, baseline MMIO, exact sourceMemory,
ordinaryDomain and sharedDomain. Header, bitmap STAR, byte packing, source
memory, domain closure, code loading, interference and every `good_init_state`
field are proved. Installation is not an additional challenge assumption.
The related machine is constructed by the actual FFI-aware bootstrap.

[NativeCompilerCorrectness.v](../theories/Baseline/NativeCompilerCorrectness.v)
applies Galette's `pan_to_target_compile_semantics`, which ends in `Qed` in the
pinned dependency. It discharges fixed-source syntax/order/allocation,
backend/machine configuration, heap arithmetic, endian and resource obligations.
The proved `read_limits` are `(2097104,1944059904)`; `538 < 2097104` removes
resource-limit relaxation. TargetTotality gives a nonvacuous terminating
behaviour and an actual finite evaluator Halt with the exact outcome/events.
Its compile/metadata/installation hypotheses are intermediate theorem inputs;
they are not inserted into `Certificate.correct`.

[BootstrapCertificate.v](../theories/Baseline/BootstrapCertificate.v) composes
native correctness with `full_bootstrap_clock_shift`, transports actual native
termination back to the common initial state, and constructs exact `Within
infinity` matching using `matchingResult_refl`. It retains unconditional baseline
admission and the original score. The committed checkpoint includes this
completion bridge, rather than an unconditional `baseline_certificate`.

The coordinator's `CertificateFromCompilation.v` was also inspected read-only.
It was **untracked in the coordinator checkout and absent from this review
base**. Its stated residual inputs are exactly:

```text
exists cprime,
 baselineCompilation = (Some (nativeCode,(bitmaps,cprime)),Some 538)
 /\ ffi_names (lab_conf cprime) = Some baselineNames
 /\ shmem_extra (lab_conf cprime) = baselineMmio
```

Its certificate proof uses the committed native-correctness and installed-state
lemmas. Inspection of this draft does not establish its integration, final
kernel audit, or an unconditional certificate.
`.artifacts/CompilationCertificate.v` seeks exactly the three conjunctions above,
not merely byte lengths or a hash. Its standalone successful completion was
announced later in this review; the library rebuild is a separate gate.

### Later coordinator completion evidence

At 03:32:53 UTC the coordinator reported session77063 exited0 with the actual
byte/bitmap/538/returned-metadata equality and four existing foundations.
Read-only inspection found its completed `.artifacts/CompilationCertificate.vo`,
the four-foundation assumption log, and
`coordinator:docs/baseline-concrete-compilation-audit.json` recording exit0 and
`actual_bytes_bitmaps_stack_and_metadata: true`. The library copy's source SHA256
matches the standalone report:
`f564b94adc736974bee96b820fb14c249f8cc0314557a0df9f920cf1b2c62e3a`.
The process monitor now says the original process is gone; process exit alone
is not used as success evidence. This review did not rerun the equality or its
kernel checker.

The coordinator also reported whole sanitized-ROM binding session14112 exited0.
Its `/tmp/rocq-baseline-literal-binding.log` says `Closed under the global
context`. This is separately reported standalone proof evidence, not a completed
verifier acceptance. The actual captured verifier literals must still be bound
in the final submitted Solution through the full isolated CLI.

Read-only inspection of the coordinator's newly prepared `BaselineCertificate.v`
found the unconditional type `Certificate baselineSubmission infinity`, proved
by destructing `concrete_compilation` and applying the conditional bridge. Its
source SHA256 is
`3b2f2634e060a58711da671a649b4f31919a36f26c9a74c3c831d03c25096d9a`.
These three certificate source files and the new compilation audit were still
untracked in the coordinator checkout, whose HEAD remained the assigned review
base when inspected. A coherent Dune rebuild was announced live; its successful
completion, the final certificate's recursive kernel context, clean integration
and positive CLI replay are not assumed. This dated update supersedes the
initial pending status of the standalone compilation and literal-binding jobs.

Recorded compiler audit [galette-audit.json](galette-audit.json) reports exactly
the existing classic, constructive indefinite description, functional
extensionality, propositional extensionality and proof-irrelevance foundations.
The full installation audit reports four of those five. The native bridge's
worker audit checked all seven declarations against only these five. Existing
recorded builds/audits were inspected; this review did not start another Rocq
build or full recursive kernel job.

## Verifier statement binding and trust boundary

[VerificationCore.v](../theories/InitE/VerificationCore.v) resolves the expected
`Certificate` before the candidate is loaded. It rebuilds the submission from
trusted `submittedCode` and `claimedScore`, keeping only candidate dispatch
metadata. The certificate must certify that rebuilt submission and the same
claimed score. A candidate cannot replace this type with `True`, certify other
bytes, or change K through a local definition/notation.

[verify.py](../verifier/verify.py) and [policy.py](../verifier/policy.py) capture
regular-file ROM and claim bytes, validate strict literal JSON and generate only
numeric `n2w` bytes and a literal finite score or infinity. Duplicate claim keys,
booleans, floats, negatives and extra fields are rejected. The ROM limit is the
original 1..128 MiB admission bound; it is not an input-blob bound. Operational
claim/source-path restrictions and resource/time limits may reject packages;
they do not relax the proposition of an accepted certificate.

The review confirmed component-wise no-follow reads, before/after file-change
checks, source rechecking after capture, and copying the exact hashed trusted
source/object bytes into a private replay tree. Candidate files and generated
literals occupy separate directories. Later comparison/kernel stages mount
both read-only; candidate compilation receives only its own writable directory.
Bubblewrap clears environment, unshares namespaces, hides host `/tmp`, and
mounts trusted libraries/toolchain read-only. Unsafe toolchain prefixes that
would expose the workspace or host temporary files are rejected. Guards reject
plugins, extraction, notation/export substitution, filesystem redirection and
load-path/Load commands, including wrappers. Those guards are supporting checks;
actual sandboxing, trusted module comparison and fresh recursive kernel checking
are independent required stages.

The checker uses `rocq check -bytecode-compiler yes -silent -o Verified.Check`.
The context parser requires exactly one summary and the expected theory/section
headers, rejects non-whitelisted axioms, type-in-type, unsafe fixpoints and
assumed positivity. All reviewed passing context reports use only the five allowed
foundations. `Inductives relying on indices not mattering` is an expected header
whose contents are not filtered by the current policy; this report does not
establish that a nonempty entry is an exploit or classify it as forbidden.
The final kernel report must be retained in full, not summarized as merely a
compiler exit code. The recorded four real CLI negatives reached their intended
module-comparison or axiom-policy gates; they were not rerun in this review.

Sealing has two concrete limits. `seal_verifier.py` checks that VerificationCore
source/object files exist and hashes the installation; it does not itself prove
source/object freshness or run the kernel checker. A seal over stale or manually
mismatched objects would not establish source fidelity. Also the seal hashes the
Rocq launcher, local/Galette `.v`/`.vo` inventory and selected build/policy files,
not the complete external worker/runtime/plugin/Stdlib/OS closure. These remain
operator-trusted even though sandbox mounts are read-only. Record and preserve
the clean build, complete context and actual toolchain alongside the seal; do
not describe a launcher hash as a complete toolchain attestation.

The current coordinator seal failed the actual read-only `check_seal()` with
`trusted file inventory differs from seal`; 17 existing sealed files also had
changed/missing bytes. This is expected rejection, not acceptance under a stale
seal. The observed seal SHA256 was
`b59b93dbbf2892c6d24ee38cb12c234a9dce0f856978a280f47a32db216b6273`.
It must be regenerated by the operator after the final verified build. This
review did not reseal or run the live compilation/package jobs.

## Concrete gaps and completion gates

| Gate | Status and required evidence |
| --- | --- |
| Exact concrete compilation | Standalone job completed during review: coordinator exit0 report, source-matching audit, compiled object and four-foundation log inspected. Require successful coherent library rebuild and final recursive kernel replay of the library theorem/certificate. Counts or hashes alone were never used to close this gate. |
| Unconditional certificate | Prepared beyond the assigned base: inspected source has `Certificate baselineSubmission infinity` with no compile/installation/source nonFail hypotheses, using the now-completed concrete theorem. Still require clean integration, coherent compilation and final full kernel context; source text alone is not successful certificate checking. |
| Fresh verifier acceptance | Pending. Build the final coherent trusted checkpoint, recursively kernel-check it, regenerate its seal, generate the original-ROM/infinity package and run the real CLI through every stage. Require exact ROM digest/950344 bytes, score `infinity`, kernel exit0, allowed full context and the final seal digest in `result.json`. Rerun the four existing real negative cases against the same installation. |
| Original semantic correspondence | Open formal fidelity obligation. Manual equation review, exact regeneration and internal Rocq compiler-target proofs are evidence, not a Lean-to-Rocq decoder/step/evaluator theorem. Include unsupported/failed/nonnative states, memory, FFI, word operations, common-constructor encoder equality, source semantics and accelerator/observation transports. The extra Galette FP guard witness must be related to original Skip, as identified in EVALUATOR-AUDIT. |
| Unspecified choices | Opaque `referenceThe` removes the earlier transparent failed-THE=ARB equation. Its Qed witness implements one permitted equal-choice interpretation; it does not prove arbitrary independent Lean choices equal. Formal transport must state a compatible interpretation and use determinism/trace-LUB uniqueness for observable guarded choices. |
| Release/provenance documentation | Pending final clean integration/main push and retained evidence. README still says no acceptance verifier yet; PORT-STATUS contains historical pending clauses now closed by committed installation/native proofs. Reconcile those claims with the final checkpoint, keeping formal fidelity and positive acceptance status explicit. This review changes neither file. |

The original reduced decoder/step formal-correspondence obligation is especially
important to the arbitrary-submission claim. Successful compiler-generated
paths do not justify silently restricting the public challenge to those paths.
No finding here authorizes weaker policy, added input bounds, assumed native
installation, invented compiler equality, or a weaker challenge statement.

## Reproduction and evidence locations

The following commands are lightweight and do not build, reseal or restart jobs:

```sh
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/audit_reference.py \
  --references-root /home/zksecurity/cv_compute/rocq-init-e --self-test
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s verifier -p 'test_*.py' -v
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/import_baseline_metadata.py \
  --references-root /home/zksecurity/cv_compute/rocq-init-e --check
rtk proxy rocq --version
rtk proxy ocamlc -version
rtk proxy dune --version
```

With populated local reference submodules, `rtk proxy env
PYTHONDONTWRITEBYTECODE=1 python3 scripts/import_baseline.py --check` reproduces
baseline literal regeneration. This review instead called its `render()` with
the clean coordinator reference root and compared the result in memory with the
worker's committed `Artifacts.v`. Literal proposal comparisons used the same
strict decimal/hex parser and read only existing native/bitmap/ROM files.

Fresh mechanical evidence: `/tmp/final-port-review-reference.json`,
`/tmp/final-port-review-literals.json`, `/tmp/final-port-review-seal.json`.
Existing installation evidence: `docs/baseline-full-installation-audit.json`.
Native bridge evidence: `/tmp/native-compiler-correctness-7m1mvf9m/validation.json`
and `assumptions.log`. Earlier real CLI evidence:
`docs/verifier-hardened-regressions.json`. Completed standalone compilation
evidence: coordinator
`docs/baseline-concrete-compilation-audit.json` and
`.artifacts/concrete-compilation-certificate.log`; literal binding log:
`/tmp/rocq-baseline-literal-binding.log`. The coordinator's newly announced
coherent build is separate; an empty/incomplete build log is not success. Temporary evidence paths are local session
artifacts, not durable release attestations; retain final reports in the release.

## Release follow-up, 2026-10-12

The previously pending coherent compilation equality, unconditional certificate,
and positive sealed recursive kernel replay now passed. The accepted result and
entire context are in baseline-positive-verifier-result.json and
baseline-positive-verifier-kernel.log; baseline-release-seal.json preserves the
747-file operator inventory. The current seal and certificate source hashes
match the accepted run. Earlier review-time seal failures and missing-proof
reports above are historical. Formal Lean decoder/step and shared-foundation
correspondence remain outstanding. Operator toolchain and runtime trust limits
still apply.
