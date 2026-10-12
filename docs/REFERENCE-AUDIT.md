# Original-reference fidelity audit

Audit checkpoint: `30ce3e13c01daa0febf115b34c70c2593f7a6dad` (SourceOrder
integration); branch `agent/reference-audit`, reviewer `rocq-verifier`.
This report compares definitions against the pinned original Lean sources.
It is a source review with reproducible provenance and regeneration checks,
not a cross-assistant equivalence theorem or a certificate for the baseline.
One specification-strength discrepancy at this checkpoint is recorded below,
with the coordinator's proposed repair and its interpretation limits.

## Authority and reproducibility

The authority is original init-e and its pinned Flapjack/riscv-zkvm dependencies.
HOL4 annotations in those files help locate definitions but are not substituted
for inspection of the Lean bodies. Galette is the implementation dependency;
proving agreement with Galette's full RISC-V model alone does not establish
agreement with the original reduced Lean model.

| Tree | Repository | Locked and observed commit |
| --- | --- | --- |
| `reference/init-e` | <https://github.com/flamingoponderado/init-e> | `b3831bc501713e27b9f6974a5eb3cd0b1ca0d2c2` |
| `reference/flapjack` | <https://github.com/flamingoponderado/flapjack> | `034bb5a1ed0b757082768d5406206bd2f8e31b7c` |
| `reference/riscv-zkvm` | <https://github.com/Verified-zkEVM/riscv-zkvm> | `afcbc45e1c74c2d296e032b5606dd977a304e8ad` |
| `vendor/galette` | <https://github.com/flamingoponderado/galette> | `6eab85e03c934eae714ecf5eb02061b55f2843c1` |

All four inspected working trees were clean, including untracked files.
They were read from the coordinator checkout because this isolated checkout's
submodules were not populated. No file in that checkout, including `_build`,
was written. All paths below are relative to the named pinned tree, unless
prefixed by `theories/`, `scripts/`, or `verifier/` (local port).

Reproduce without builds, compiler evaluation, or resealing:

```sh
rtk proxy python3 scripts/audit_reference.py \
  --references-root /home/zksecurity/cv_compute/rocq-init-e --self-test \
  > /tmp/reference-audit.json
```

With local pinned submodules available, omit `--references-root`. The script
checks clean commit provenance, regenerates four imported files **in memory**,
checks AST declaration coverage and ASCII names, evaluates all 20 layout
parameters independently, compares startup words and accelerator tables/moduli,
and emits SHA256s identifying the local semantic surface. Exit zero means these
specific checks passed. It does not mean all semantic fidelity obligations are
closed. `open_obligations` is deliberately present in successful output.

## Open finding: failed THE and independent arbitrary choices

Pinned Flapjack `Flapjack/Misc/Option.lean` defines `holThe none` using the
opaque carrier-specific `holTheNone`. `Flapjack/HolArb.lean` independently defines
opaque `holArb`. Neither definition identifies these two choices.
Original `Flapjack/Compiler/Encoders/RiscV/Target/State.lean` uses `holThe` in
`riscvNext`. Local `theories/Target/Configuration.v` uses Galette `THE`, whose
`None` branch is `ARB` in `theories/HOL/src/coretypes/option.v` under Galette.
Thus Rocq has the definitional equation `THE None = ARB`; Lean has no analogous
link between `holTheNone` and `holArb`.

This is a concrete difference in the treatment of unspecified values, not a
proved execution counterexample or evidence that the two choices must differ.
Choosing them equal is one possible interpretation. An exact fidelity claim
must explain that interpretation, or retain independent choices and coordinate
any affected proof changes. It must not silently use the stronger Rocq equation
as an equation supplied by the original Lean specification.

The issue is relevant outside successful compiler-generated steps: arbitrary
admitted ROM can take `NextRISCV` to `none`; the target evaluator computes
`next`, then checks state validity and interference for the resulting state
(Galette `theories/cakeml/compiler/backend/semantics/targetSem.v`,
`evaluate_body` and `evaluate`). Validity of the old state does not alone make
the arbitrary successor irrelevant. This finding was sent immediately to
`rocq-main`; no shared target/proof files were changed by this audit.

During review, the coordinator announced a repair in a separately owned
`Target/ReferenceChoices.v`: an opaque `theNone` defined with `Qed` from an
`ARB` witness, and transparent `referenceThe` dispatching Some/None. If opacity
is retained, the independent proof-visible interface is preserved without a
new axiom; equality to `ARB` is no longer available by reflexivity. The witness
selects a permitted equal-choice interpretation internally. It does not prove
that arbitrary independently chosen Lean constants are equal. This audit base
does not contain that repair; its integration, successful-step proofs, opacity
checks (including extraction behavior), and kernel assumptions must be checked
separately before closing the finding.

Two superficially related occurrences have different conclusions:

* The address `THE` in original physical instruction fetch receives `some`
  for every state: the reduced `translateAddr` always succeeds unchanged.
  Its failed-choice branch is unreachable in this model, without a state
  validity premise.
* Original `setTrap` starts from `holArb SynchronousTrap` but overwrites both
  fields (`trap`, `badaddr`). Local construction of the two-field record
  removes no observable choice. The omitted floating-register getter is
  instead retained as a projection of an arbitrary **whole target record**;
  it is not replaced by zero. Its supplied inhabited witness is not `ARB`.

## Fixed guest AST and source binding

Original `reference/init-e/Guest/Ast.lean` is the literal authority, not the
Pancake text parser, an extracted image, or another guest evaluator.
Its SHA256 is
`21925d793b4159c30406a4d48a7402d4a2cdc23e0189201342aa89778d4534ed`.
`import_guest.py` reproduces `theories/Guest/Ast.v` byte for byte (local SHA256
`53f716bbaf9df4d84d1252eb6050dd79b8b907d55c00bb6cb2e92f516b0e9f6e`).
All 929 `def` headers are covered by the importer; all 30,942 string occurrences
have ASCII contents. The literal's identifiers therefore have an injective
encoding into Galette `mlstring`.

The constructor map was reviewed against Flapjack
`Flapjack/Pancake/PanLang/{Decl,Prog,Exp,Shape}.lean` and Galette
`theories/cakeml/pancake/panLang.v`. The relevant production-to-HOL codecs map
names with `ofString`, preserve constructor payloads, and right-associate
products. The importer preserves function `inline`, `exported`, parameters,
body, return shape; maps `exported`/`returnShape` to Rocq field names; maps
64-bit constants with `n2w`; translates local/global variables, structures,
loads, operators/comparisons/shifts, declarations, sequencing, branches/loops,
calls, exceptions, return, and shared-memory operations. In particular a call
with `none` remains the no-return-metadata `Call None` constructor.
The importer is specialized to this pinned syntax, not a general Lean parser:
unknown dotted constructors are rejected, but bare names and header recognition
are not a general fail-closed grammar for future Lean programs.

`InitE/SourceSemantics.lean` explicitly uses `guestAst.map declToHOL` and the
compiler theorem's declaration evaluator. Local `SourceSemantics.v` uses the
imported literal with Galette `semantics_decls`; it does not use the stepped
`Guest.Model` program evaluator. `SourceDeclarations.v`/`SourceOrder.v` prove
that moving the last function `main` to the front preserves this literal's
semantics, including earlier globals/exceptions/names and arbitrary input.
This is an internal Rocq transport theorem, not a Lean-to-Rocq evaluator theorem.
The latter foundational obligation remains separately identified below.

## Reduced carriers, defaults, decoder and operations

`Flapjack/RiscV/L3/Types.lean` has 38 carrier declarations, 114 record fields,
and 109 inductive constructors. `import_reduced_types.py` preserves every
field, constructor order, width, and right-nested product in `ReducedTypes.v`.
`Nat` becomes unbounded `N`, `HolChar` becomes 8-bit `ascii`, maps remain
functions, and options/lists retain their constructors. Derived defaults were
reviewed: records are fieldwise default, inductives use their first constructor
(with default payload), bits/naturals/chars are zero, booleans false, lists
empty, options none, functions constant default. In particular the *default*
exception is `INTERNAL_ERROR []`, not `NoException`; initialization explicitly
sets `NoException`. Default values must not be confused with unspecified `ARB`.

Original `Defs/Decode.lean` SHA256:
`6bcc43b5a876ea85935e1fdf14fe9e02dc5010dc8c1a6386445d1be556fc1b99`.
Both `ReducedDecode.v` and the companion full-carrier `Decode.v` regenerate
exactly. `DecodeBits.lean` reads bits 31 down to 0; local bindings retain that
order. `DecodeImmediates.lean` concatenations are preserved: branch immediate
1+1+6+4, jump 1+8+1+10, store 7+5, with no premature signed interpretation or
extra offset bit. `Support.lean`'s `holV2w` orders the list most significant
bit first, matching `v2w`. `DecodeRVC` remains unknown. No compressed,
floating-point, atomic, CSR, or omitted word-op extension is inserted.

The following table records manual equation comparisons. Original paths in
this table are under `reference/flapjack/Flapjack/RiscV/L3/`; local paths are
under `theories/Target/`. Shared word operations were read from pinned Galette,
including signed quotient/remainder (magnitude division with sign correction,
truncating toward zero), resizing/sign extension, and bounded bit indexing.

| Original source | Local definitions | Semantic cases reviewed |
| --- | --- | --- |
| `Defs.lean` | `ReducedStateOps.v` | Current `procID`, nested functional updates, zero-register reads/writes, `NextFetch`, complete two-field trap overwrite; no invented delta updates. |
| `Defs/IntegerLoadMode.lean`, `MMU/Exception.lean`, `Defs/WordArithmetic.lean` | `ReducedMode.v` | Architecture codes 0/2/3, code 1 records first undefined exception, decimal message; returned mode state retained; ADDIW illegal in RV32, otherwise low32 of width64 sum sign-extended. Unspecified results require the choice interpretation discussed above. |
| `Defs/RegisterALU.lean`, `Defs/ImmediateALU.lean` | `ReducedRegisterALU.v`, `ReducedImmediateALU.v` | ADD/SUB/XOR/OR/AND and immediate forms are width64 with no inserted architecture query; immediates sign-extended from 12 bits. |
| `Defs/Multiply.lean` | `ReducedMultiply.v` | MUL full64; high unsigned/signed/mixed products at width128; three mode queries in high forms, exact 32/64 high extraction and zero/sign extension. |
| `Defs/Divide.lean` | `ReducedDivide.v` | DIV/DIVU/REM/REMU, zero divisor results, signed overflow wrap; original RV32 operand widths and DIVU's second query, no absent W variants. |
| `Defs/RegisterShift.lean`, `Defs/ImmediateShift.lean` | `ReducedShift.v` | RV32 SLL deliberately shifts full64 with low5 count; SRL/SRA narrow low32 then zero/sign extend; RV64 low6; immediate bit5 illegal in RV32; repeated queries retained. |
| `Defs/SetLess.lean` | `ReducedSetLess.v` | Two-query register forms; unsigned RV32 SLTU zero-extends low32 whereas SLTIU sign-extends low32; signed12 immediate and singleton boolean-to-word. |
| `Defs/ConditionalBranch.lean` | `ReducedBranch.v` | Six conditions, both RV32 operands sign-extended even for unsigned branches; two mode queries; second returned state's PC; no added alignment trap. |
| `Defs/UpperJump.lean` | `ReducedUpperJump.v` | JAL/JALR link PC+Skip, signed offsets, JALR clears bit0; original bit0 trap test; LUI sign-extended width32, AUIPC adds PC. |
| `Defs/IntegerLoad.lean` | `ReducedLoad.v` | LB/LBU/LH/LHU/LW/LWU/LD widths and extensions; mode guard only for LWU/LD; Data/Read, signed offsets and state threading on faults. |
| `Defs/IntegerStore.lean` | `ReducedStore.v` | SB/SH/SW/SD byte counts 1/2/4/8, signed offsets and Data/Write; mode guard only SD. |
| `MMU/Access.lean`, `MMU/Primitives.lean`, `Defs/ReadInst.lean` | `ReducedMemory.v` | Physical translation always some, Mbare; little-endian MEM; aligned word indices wrap at 61 bits; unaligned read uses arithmetic shift of width128; partial store mask and cross-word high-then-low writes; all byte counts preserved; instruction length from low bits, Skip2/4 on current core. |
| `Defs/SystemSignals.lean`, `Defs/ControlFetch.lean` | `ReducedSignals.v` | Four 2-bit privileges, illegal/breakpoint/environment signals, ECALL uses MPRV; fetch fault/misalignment bad-address payloads. |
| `Defs/Run.lean`, `Step/Next.lean` | `ReducedStep.v` | Every reduced dispatch case; FENCE identity, unknown illegal; Half unknown/Word decode; fetch-run-exception order; sequential PC+Skip, BranchTo clears NextFetch, Trap returns none; no added post-step alignment test. |

The decoder/step/encoder agreement proofs with Galette native64 are valuable
internal verification, especially for compiler-generated successful steps.
They do not replace the source comparisons above, and their `riscvOk` premises
do not justify an all-state claim about failed or nonnative steps.

## Configuration and initialization

Compared original Flapjack
`Compiler/Encoders/RiscV/Target/{Configuration,State}.lean` against local
`Configuration.v` and Galette `riscv_target.v`: seven-component projection,
all five validity conjuncts, current-core getters and modulo-5 register names;
ISA RISC-V, 32 registers, avoid `[0,2,3,4,31]`, no FP registers, link 1,
little endian, alignment 2, no two-register arithmetic. Immediate bounds keep
Sub's strict lower bound; byte/halfword/address offsets are -2048..2047;
jump/location bounds -2^31..0x7FFFF7FF; conditional jumps -2^20+8..2^20-1+4.
Encoder correctness uses the existing complete byte encoder through reviewed
reduced dispatch proofs. The unspecified getter/failed step distinction is
recorded in the open finding.

Compared init-e `InitE/{Parameters,SubmissionModel,SubmissionAdmission,
SubmissionInitialization,MachineInitialization}.lean` with corresponding local
files (admission/initialization also reside in `SubmissionModel.v`). All 20
layout constants/formulas agree independently, as do the five literal
`Guest/Bookkeeping.lean` startup headers. Code/input arenas are 128 MiB, output
is 64 KiB, ordinary RAM starts at 0xa0000000 with size 29 GiB, source base
0xa1000000, stack 16 MiB, globals 93 words, and gas cap 200,000,000.

Reviewed every admission field: nonempty bounded ROM, strict anchor bounds,
alignment, name boundary and external/shared classifications, metadata length,
loaded ordinary dispatch slots, MMIO validity/register/exit constraints,
distinct loaded aligned entries, halt/cache exclusions, MMIO program binding,
loaded exits, and layout bound below 2^64. Lean bounded `Fin` quantification is
represented by `N` plus the same bound. No admission conjunct was removed.
Initialization keeps shared input/output memory priority, ROM elsewhere then
zero, current-core PC/register hooks, all-core initial PC, VM0/MPRV3/ArchBase2,
zero GPRs, none NextFetch and explicit NoException; other fields retain defaults.
FFI registers 10/11/12/13, saved 24/25/26, halt/cache slots, ordinary and MMIO
entries/exits, callback lookup, and identity interference agree. Returned byte
writes recurse tail first, so earliest bytes win at wrapped addresses, matching
Flapjack `Misc/AsmWriteBytearray.lean`.

## Input, FFI, accelerators and observations

Original init-e `Guest/{Basic,GasLimit,Model,AccelFfi,Accel}.lean`
were compared with the local Guest files and `SourceSemantics.v`.
Short input reads return zero; request offset is `2 + le32(input,2)`, payload
adds `le32` at that request, and gas is `le64` at payload+412. There is no new
schema-validation or input-length premise. Host bytes are eight zeros, encoded
64-bit length, input, then alignment padding. Only the bounded input arena is
mapped, so oversized input is truncated by the mapping; output starts zero.
Reads/writes retain width/config decoding, short-list saturating subtraction,
wrapped addresses, mapping checks and the original update predicates.

The source oracle makes `halt` and `trap` terminal **failed** events; this
explicitly overrides the returned runtime calls of `Guest.Model.guestOracle`.
Byte-string conversion is `toStringOfBytes`, not a UTF8 replacement decoder;
its inverse `ofString` preserves arbitrary byte names, so direct comparison
with the known ASCII accelerator names is faithful.

All 18 accepted accelerator names and their argument/config guards were
reviewed against `Guest/AccelFfi.lean`: empty configuration, exact word counts,
Keccak 25, SHA 12 and preserved block suffix, arithmetic 4/6-limb packing and
nonzero modulus, curve coordinate/range/distinct-x or nonzero-y guards,
Fp2 component bounds and preserved second argument, BLAKE 33 words and index<10
with preserved index/message. Unknown or malformed calls fail.
Pure definitions were compared directly against pinned riscv-zkvm
`RiscvZkvm/Rv64/ZiskAccel.lean`: Keccak theta/rho/pi/chi/iota and 24 rounds,
SHA schedule/compression/feed-forward and byte swaps, little-endian limbs,
512-fuel modular exponentiation, chord/tangent formulas with natural saturated
subtraction, Fp2 multiplication's p*p padding, BLAKE mixing and update indices.
The script independently compares all 24 Keccak constants, 64 SHA constants,
10x16 BLAKE permutations, 5x5 rho offsets and three field moduli.
These checks and existing known-answer tests support review; neither proves
all-argument cross-assistant accelerator equality. The hardware CSR/memory
wrapper in riscv-zkvm is not the oracle definition used by init-e.

Compared `InitE/{Observations,NatE,Challenge}.lean` with local counterparts:
output byte32=1 means accepted; accepted source requires all 65,536 output
bytes equal; other covered outcomes require covered nonaccepted target.
ResourceLimit is uncovered. Trap classification retains the 1/6/7-byte config
exceptions; terminal halt remains normal. Host replay folds event order and
returned bytes. Infinity requires an input-dependent **finite** witness;
finite score bounds that witness. The certificate quantifies over every input
with declared gas <=200,000,000, every terminating source result and covered
outcome; there is no added input-size or target-state premise.

`VerificationCore.v` reconstructs `Build_Submission` from trusted
`submittedCode` and `claimedScore`, retaining only participant anchor/names/
first/extra metadata. Its candidate certificate therefore cannot certify
another ROM or K. `verify.py` reads byte/claim snapshots, generates `Values.v`
using `policy.literal_module`, and checks that interface in the sealed replay.
The score parser permits exactly a natural or infinity. Existing source guards,
assumption allowlist and trusted sealing were reviewed/fixed earlier; this audit
changes no challenge, proof, policy, reference, or trusted object and runs no
full verifier/reseal. No verifier success for a complete baseline is claimed.

## Remaining work and limits

1. Resolve/document the independent failed-THE choice interpretation before
   asserting complete fidelity on arbitrary target executions. Also keep the
   canonical arbitrary-whole-record getter interpretation explicit.
2. The carrier/operator correspondence for the full shared evaluator libraries
   is a foundational review obligation. This report reviews the fixed AST,
   challenge wrappers and relevant word operations, but does **not** claim a
   complete clause-by-clause audit or cross-assistant theorem for Flapjack's
   entire finite-map Pancake evaluator versus Galette `panSem`, or all of
   `evaluateTargetHOL` versus Galette `targetSem`. Their common HOL lineage and
   internal proofs are evidence, not a substitute for that remaining comparison.
3. All-argument pure accelerator transport theorems are absent; source review
   and table comparison are the evidence here. Original `InitE/OracleReplay.lean`
   also has physical-host/replay proof infrastructure without a corresponding
   standalone port module at this checkpoint.
4. This audit is not a review of every compiler pass or the original baseline
   certificate. Coordinator-reported native extraction is a proposal until its
   concrete result is bound by kernel-checked equality; the full baseline
   certificate and live sealed CLI replay remain separate completion criteria.
5. Hash/regeneration checks detect drift for this fixed syntax. They do not
   validate arbitrary future importer syntax, establish truth of a theorem,
   or enlarge the verifier's allowed assumption set.

Validation performed on this branch: read-only audit script succeeds against
all four clean pinned trees; isolated corruption regressions reject AST,
parameter and accelerator-table changes. No Rocq compiler job was started.

## Coordinator repair validation

After integration, `Configuration.riscvNext` uses `referenceThe`. Its failed
branch is a distinct opaque `Qed` witness in `Target/ReferenceChoices.v`;
successful Some dispatch remains transparent. `ReferenceChoiceTests.v` rejects
opening the witness with `Transparent` and rejects equating it to ARB by
reflexivity. The full coherent Dune build passes, including the reduced encoder
and machine-configuration proofs. This closes the extra proof-visible equation
finding under the equal-choice interpretation described above. It is not an
all-interpretations Lean/Rocq choice correspondence theorem. Native proposal
extraction does not include target next callbacks (`NativeCompilation.v`);
those callbacks must not be used as an extracted challenge verifier.
