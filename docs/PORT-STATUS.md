# Port status

The goal remains a complete port of original init-e pushed to `main`.
A passing module build is not evidence of a baseline certificate or of
acceptance by an isolated submission verifier.

## Implemented, requiring final port review

| Rocq module | Original reference |
| --- | --- |
| InitE/NatE | InitE/NatE.lean |
| InitE/Parameters | InitE/Parameters.lean |
| Guest/Ast | Guest/Ast.lean; reproducible importer |
| Guest/GasLimit | Guest/GasLimit.lean |
| Guest/ByteCodec, Guest/AccelFfi | Guest/AccelFfi.lean |
| Guest/Accel | riscv-zkvm v0.3.0 Rv64/ZiskAccel.lean pure definitions |
| Guest/Bookkeeping | Guest/Bookkeeping.lean |
| Guest/HostMemory | Guest/Model.lean host framing and mapped handlers |
| InitE/SourceSemantics | InitE/SourceSemantics.lean |
| InitE/Observations | InitE/Observations.lean |
| InitE/SourceDeclarations | InitE/SourceDeclarationsCore.lean |
| InitE/TargetTotality | InitE/TargetTotality.lean using Galette machine_sem_total |
| Target/Decode | Flapjack L3/Defs/Decode.lean; literal importer |
| Target/Step | Flapjack L3/Step/Next.lean outer equation |

The challenge target now uses the directly ported original reduced interpreter.
The earlier full-model restricted-step modules remain compiler-bridge tools.
Reduced Lean decoder/step agreement review and the compiler-target simulation
are still explicitly outstanding.

The list-recursive gas reader has an explicit equality proof against standard
indexing. It preserves zero-padding semantics while avoiding construction of
huge unary indices when a short input declares an enormous SSZ offset.

## Required before completion

1. Review literal importer fidelity and all manually ported definitions.
2. Complete reduced target primitive/model agreement and compiler-target
   simulation; unsupported instructions must retain original behavior.
3. Port concrete machine initialization, MMIO/FFI metadata and admission.
4. Instantiate the exact original certificate statement with fixed source and
   target semantics. Infinity must still require finite matching termination.
5. Compile the authoritative guest, kernel certify bytes/bitmap/configuration
   equality and static stack bounds, and prove installation/bootstrap/layout.
6. Compose Galette's correctness theorem into the baseline certificate. Its
   resource-limit extension must be eliminated by the proved stack bound.
7. Implement isolated submission checking, immutable trusted-file manifests,
   literal bytecode/score sanitization, an axiom whitelist, and kernel checking
   of the proof against the fixed statement. Add genuine negative CLI tests.
8. Run full baseline verification, record actual tool versions and artifacts,
   review and push the completed port to main.

The fresh pinned Galette dependency build passed. `InitE/CompilerAudit.v`
was compiled independently against that build and printed exactly the five
classical foundation axioms recorded in `galette-audit.json`. There are no
additional assumptions in the top-level compiler theorem. This does not
certify the concrete init-e baseline.
Floating-point stand-ins in Galette must remain unreachable under the reduced
challenge decoder; excluded FP instructions cannot become accepted submissions.

## Current proposed artifacts

The pinned extracted Galette compiler successfully compiled original
`Guest/guest.pp.pnk` with `--pancake --target=riscv`, producing 4,987,468 bytes
of assembly in `.artifacts/guest.riscv.S`. This is a compilation proposal,
not a proved ROM or a challenge certificate. The compiler warnings are saved
in `.artifacts/guest.compile.log`.

`Target/DecodeAgreement.v` passed kernel checking: for every 32-bit word,
the literal original decoder equals the explicit restriction of Galette's
decoder. The proof distributes the restriction through the original branch
tree and finishes by reflexivity; it does not enumerate all bit patterns.
The supported-instruction step bridge also passed kernel checking: the two
step functions agree when the fetched word decodes to a supported instruction.
This is a baseline simulation lemma, not a restriction on submissions.

The implemented source/observation modules, all accelerator known-answer
tests, restricted decoder boundary tests, and target totality helper passed
an isolated Rocq compilation against the freshly built Galette dependency.
The fixed-source global count, unique names/parameters, exception bound and
good-panops obligations passed too. `good_panops` contains a classical
quantified predicate; `SourceFacts.v` proves it equal to an executable arity
checker before computing. The complete Dune build remains a separate pending gate.

## Reduced machine and fixed statement

The original reduced carriers are now generated field for field from pinned
`Types.lean`, including right-nested products. The original physical-only
translation, unaligned memory operations, arithmetic/mode/control cases and
complete interpreter step are ported directly. `Configuration.v` and native
callbacks now use these reduced carriers. Failed THE and the omitted FP
getter select from the original reduced types, not the full model.

`SubmissionModel.v` ports the participant fields, original admission clauses
and zeroed initialization. `Challenge.v` ports the exact certificate shape
and derives infinity certificates from exact behavior preservation using
proved machine totality. The declared gas premise remains 200M, and no
input-size premise was added. All current modules and reduced interpreter
regressions passed a full Dune build. These facts do not supply a baseline
certificate: compiler-target simulation, concrete compilation/install proofs
and isolated submission verification are still required.

`InstructionEmbedding.v` proves that the directly generated reduced decoder
embeds into the earlier checked restricted decoder for every 32-bit word.
`StateEmbedding.v` is the reduced-to-full compiler-model bridge; its extra
fields exist solely in the proof embedding, outside the challenge carrier.
Full reduced Lean decoder/step agreement review remains explicitly
outstanding until the reference primitives have been reviewed and the
compiler-target simulation has been proved.

## Independent kernel check and compilation in progress

`rocq check -bytecode-compiler yes -silent -o ... InitE.InitE.Challenge`
passed exit0. Its full context contains exactly the five foundation axioms
in `challenge-kernel-audit.json`, with no type-in-type, unsafe fixpoints or
assumed positivity. The context is recorded in `challenge-kernel-check.log`.

`BaselineCompiler.v` defines compilation of the authoritative AST using the
original Pancake/RISC-V configuration. A VM computation of native byte count,
bitmap count and static stack result is running; it is separate from the
earlier text-based assembly proposal and is not yet a compilation proof.

The verifier currently has literal/kernel-policy checks and six security
regressions. The real sandboxed CLI and immutable source/artifact sealing are implemented.
Wrong statements, mismatched ROM, mismatched score and axiom-backed
certificates were rejected by their intended gates. Successful baseline
acceptance and final adversarial integration review remain outstanding. A minimal
Bubblewrap namespace/isolation capability check passed on this server.

`StateAgreement.v` now proves GPR, PC, memory and validity agreement with the
Galette model and equivalence of the assembly-state relation. Instruction
execution/encoder correctness transfer and the concrete baseline proof are
still required.

## Reduced compiler-model bridge progress

The checked arithmetic, immediate, multiplication/division, shift, branch,
upper-immediate and jump simulations are composed in `RunAgreement.v`.
All seven integer loads and interpreter signals are checked. Memory reads
include unaligned cross-word accesses; physical translation follows from
original validity. Fetch preserves validity. `NextAgreement.v` composes
these results into reduced outer-step agreement with an explicit store
simulation obligation. `TargetProperties.v` proves the reduced `target_ok`
property through the original projection embedding. These are local build
results, not a complete encoder correctness or baseline certificate.

Verifier hardening from worker branch `agent/verifier-review` was reviewed
and integrated as `a56baac`; all 18 Python regressions passed independently.
It snapshots participant inputs and sealed trusted libraries into private
replay directories, rejects unsafe source commands and parses kernel context
sections strictly. The current operator seal needs regeneration after the
final coherent build; full baseline acceptance remains outstanding.

## Completed reduced step composition

Worker stores were reviewed and integrated as `83e1c33`; their independent
kernel replay used only the existing five foundation axioms. A coherent full
Dune build then passed with all four store simulations, memory writes,
`NextAgreement.reduced_next_embedding`, static machine initialization and
register permutation inverse facts. Reduced step agreement is now proved on
original valid states against the restricted full model. Transfer to the
unrestricted compiler target still needs support facts for encoded paths and
the complete encoder correctness proof. Reference-definition fidelity review
remains outstanding; this result is not a concrete baseline certificate.

All four real hardened CLI negative cases passed: wrong statement, wrong ROM
and wrong score fail trusted module comparison, and an axiom-backed exact
certificate fails kernel policy. Results are recorded in
`verifier-hardened-regressions.json`. Static configuration facts retain
encoder correctness as an explicit obligation. Guest AST compilation is
still live, and no positive baseline verifier result or main push is claimed.

## Compiler application premises now proved

`BackendConfigFacts.baseline_backend_configuration` proves the full concrete
`backend_config_ok` predicate. `MachineConfigFacts` proves register
initialization and reduces machine configuration correctness to the remaining
encoder theorem. `SourceAllocation.source_globals_allocatable` proves global
allocation for every input; no input-size assumption is introduced.
`BaselineLayout` proves the fixed heap/stack arithmetic.

`CompilerStepBridge` transfers successful supported steps, preserving the
original distinct canonical values on failed THE. `EncoderSupport` passed
independent full kernel replay with exactly the existing five foundation
axioms, was reviewed and integrated as `465bb33`, and passed coherent Dune
compilation. `ReducedEncoderStep.reduced_one_step` transfers abstract
instruction correctness and the memory-frame property to the reduced target.
Complete arbitrary-interference paths and per-assembly-case encoder
correctness remain required; the worker is auditing its path proof branch.

Concrete guest compilation, native installation/bootstrap, the actual stack
certificate, source declaration-order behavior transport, final reference
fidelity review and positive full verifier acceptance remain outstanding.

## 2026-10-12 checkpoint

Later work supersedes the earlier pending compiler-bridge notes above:
`ReducedEncoderCases.reduced_riscv_encoder_correct` and
`MachineConfigCorrect.challenge_machine_configuration` are now proved and
pass the coherent Dune build. `SourceOrder.v` proves preservation when moving
this fixed literal's main declaration to the front. The latest full build also
passes the independent opaque failed-THE interface regressions.

The exact literal-AST compilation form in `NativeCompilation.v` is proved equal
to `baselineCompilation`; extraction of that form produced an **untrusted
proposal** of 904,196 native bytes, 4,614 bitmap words and stack maximum 538.
Native SHA256: `21e4ad09c0b75c4e7d79ea8945cca480edad6b34410099ffff8760a08158c34e`.
Bitmap SHA256: `1ff90e1caf1c69e47f3b9ece79a99e74884e9511f14e822bbc6f090bca020277`.
The symbolic compilation-form equality does not certify those literal bytes.
The original VM count diagnostic remains live; it is not a compilation equality
proof. Native reduction is disabled in the installed Rocq build and falls back
to VM reduction.

`REFERENCE-AUDIT.md` records the pinned source review and remaining foundation
obligations. Its regeneration/provenance tests and isolated corruption tests
pass. The original reduced decoder/step source review has concrete evidence,
but complete cross-assistant correspondence remains explicitly outstanding.
The opaque failed-THE repair removes the extra proof-visible equality to ARB
without adding a new axiom; its equal-choice interpretation is documented.

Still required: kernel binding of actual compiler output, concrete original
five-header bootstrap and installation/admission proofs, resource bounds,
complete baseline certificate and positive sealed CLI verification. No main
push or baseline-verifier success is claimed by this checkpoint.

The reproducible `scripts/compare_baseline_proposal.py` comparison confirms
that native bytes and bitmaps are identical to original pinned Lean literals.
The original full ROM extracted from those literals is 950,344 bytes, SHA256
`22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc`.
These comparisons do not replace a kernel compilation equality or certificate.

### Original literal and bootstrap checkpoint

`Baseline/Artifacts.v` imports only the pinned original byte and bitmap
literals, through `scripts/import_baseline.py` with clean-reference/pin checks.
`ArtifactFacts.v` proves actual ROM/native/bitmap sizes and binds the first208
ROM bytes to the verified original bootstrap encoder output. Explicit splits
and lazy reduction avoid unnecessary byte-value normalization for size facts.
The coherent full Dune build passes with these modules.

`BootstrapProgram.v` proves exact208-byte encoder agreement, instruction
admission, and original23132 assembly-step count. `BootstrapSteps.v` lifts
checked assembly traces to the real reduced target and FFI-aware evaluator.
`BootstrapComposition.v` proves finite clock-shift composition and termination
transport. `BootstrapPrefix.v` proves the three address loads reach the actual
copy-entry state and relates checked instruction lists to finite assembly
traces. `BootstrapMemory.v` defines the original expected installed state;
its reachability is still to prove, not assumed by the challenge.

Remaining concrete bootstrap work includes installed-byte/domain proofs,
checked prefix, symbolic bitmap-copy loop, tail writes/control, shared-input
frame, and the final installed-machine relation. The full concrete compiler
output equality, complete certificate and positive sealed verifier gate remain
open. The source evaluator audit is now integrated as `EVALUATOR-AUDIT.md`,
with its source-review evidence and formal transport limits retained.

### Original submission and copy-word checkpoint

`Metadata.v` imports the original pinned compiler-config FFI/MMIO literals.
`MetadataFacts.v` proves all finite dispatch/layout obligations and passed a
full recursive kernel check with exactly the existing five foundations and
no unsafe declarations. `Submission.v` uses the original literal ROM,
infinity score and metadata. `SubmissionFacts.baselineSubmission_admitted`
proves **every** original admission field unconditionally, using actual
literal lengths. The full coherent build with these files passes.

`BootstrapCopy.v` now proves the actual LD/SD pair copies each of its eight
source bytes, frames every other byte, and succeeds under exactly the source/
destination domain and alignment obligations. Opaque assertion/store helper
lemmas avoid unnecessary expansion of nested state records in conversion.

The original VM count probe exited0 with Some(904196,4614,Some538). It is
count evidence only. A separate concrete byte/bitmap/configuration equality
proof is live, including original FFI/MMIO metadata, under112GiB address-space
and10800s timeout. That proof has not yet passed. Monitor:
`/tmp/rocq-concrete-compilation-state.json`; log:
`.artifacts/concrete-compilation-certificate.log`. The full loop/tail trace,
installed relation, complete certificate and positive sealed verifier remain
open; no completed-port or main-push claim is made.

### Checked prefix and loop composition checkpoint

`BootstrapCodeFacts.v` proves every original block's actual encoder bytes are
loaded at its declared ROM address and inside the unchanged executable domain.
It proves a checked assembly prefix trace from initialAsm to copyEntryAsm.
`BootstrapMemoryControl.v` proves PC updates commute with memory operations;
`BootstrapCopyLoop.v` defines exactly the original five-instruction body and
proves its load/store pair advances PC by8 while performing copyWord.
All current modules pass the coherent full Dune build. The full4617-iteration
loop and tail/installation composition remain to prove; no baseline certificate
or positive verifier acceptance is claimed here.
