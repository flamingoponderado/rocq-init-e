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
regressions. The real sandboxed CLI, immutable manifest, successful baseline
package and end-to-end acceptance gate are still outstanding. A minimal
Bubblewrap namespace/isolation capability check passed on this server.
