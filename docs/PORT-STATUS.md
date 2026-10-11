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

The target step currently reuses Galette's integer instruction primitives.
Agreement with original reduced Lean primitives is **outstanding**. The
original decoder is translated directly; Galette's unrestricted decoder is
not used to admit arbitrary submitted instruction encodings.

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
