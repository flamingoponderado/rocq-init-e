# Original finite-map and target evaluator audit

Reviewer: `rocq-verifier`; branch `agent/evaluator-audit`.
Reviewed port checkpoint: `415eac74844864b33a51b8d3dcc5e9b6553caee2`.
This is a clause-by-clause comparison of executable definitions, not a
cross-assistant equality theorem. No new behavioral discrepancy was found in
the compared width64 evaluator clauses. An assembly-carrier difference and
remaining transport obligations are recorded explicitly below. No build,
compiler evaluation, verifier replay, reseal, or shared proof edit was performed.

## Provenance, scope and carriers

Source authority is the original Lean challenge's actual call graph:

* init-e `InitE/SourceSemantics.lean` calls
  `PanSemStateFiniteExact.semanticsDecls` on
  `Guest.guestAst.map Pancake.PanLang.declToHOL`.
* Its finite-map evaluator is defined in Flapjack
  `Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean`, through
  `evaluateHOLFiniteStateWithDeciders` and
  `evalPanSemRecursiveCallFiniteContext`. The outer assembly-marker option is
  always populated (`evaluateHOLFinite_ne_none`); its fallback is not an
  extra runtime result. `EvaluateFinite.lean` supplies clause equations.
* Expressions use `evalHOLFinite`, which projects finite-map state through
  `toExact` into `EvalExact.lean`'s `evalHOLExact`.
* init-e `InitE/Challenge.lean` calls Flapjack
  `evaluateTargetHOL` from
  `Flapjack/Compiler/Backend/Semantics/TargetSem/Evaluate.lean`.
* The port calls pinned Galette `panSem.{eval,evaluate,semantics_decls}` and
  `targetSem.{evaluate,machine_sem}`. It does not replace either with an
  executable guest model, parser, or extracted evaluator.

Locked commits (also observed clean, including untracked files):

| Tree | Commit |
| --- | --- |
| `reference/init-e` | `b3831bc501713e27b9f6974a5eb3cd0b1ca0d2c2` |
| `reference/flapjack` | `034bb5a1ed0b757082768d5406206bd2f8e31b7c` |
| `reference/riscv-zkvm` | `afcbc45e1c74c2d296e032b5606dd977a304e8ad` |
| `vendor/galette` | `6eab85e03c934eae714ecf5eb02061b55f2843c1` |

The pinned files were read from `/home/zksecurity/cv_compute/rocq-init-e`;
that checkout and its `_build` were never written. Paths abbreviated `Pan/`
below mean `reference/flapjack/Flapjack/Pancake/Semantics/PanSem/`;
`Target/` means
`reference/flapjack/Flapjack/Compiler/Backend/Semantics/TargetSem/`;
`G/` means `vendor/galette/theories/`.

The correspondence is at the challenge's fixed word width64. Nat clocks,
indices and shape sizes correspond to unbounded Rocq `N`; words correspond
through their unsigned value modulo 2^width; `BitVec 8`/`UInt8` correspond to
Rocq word8/ASCII as appropriate. Lean tuples are right associated; the Rocq
return pair is `(result,(machine,ffi))`. Shapes, values, byte names and FFI
constructors are related constructor by constructor, rather than by incidental
constructor order or inhabited defaults. Runtime result `none` is normal
completion; it is distinct from failed assembly or failed expression evaluation.

Both finite-map carriers are total option-valued lookup functions with finite
support proofs: Flapjack `Pancake/Semantics/CrepSem/HOLState.lean`'s
`HolFiniteMapExact`, Galette `HOL/src/finite_maps/finite_map.v`'s `fmap`.
Support proofs have no runtime observation. `FEMPTY`, keyed update, deletion,
lookup and left-fold ordered update-list agree pointwise. `resVarEq`/`res_var`
erase absent original bindings and restore present original bindings. Maps
are not replaced by arbitrary functions without the finite-support invariant.
`StateExactFiniteMap.lean`'s `toExact`/`ofExact` wrappers have roundtrip facts;
classically chosen memory-domain deciders add no predicate or runtime guard.
The 13 state fields have matching meanings, including total word-cell memory,
ordinary/shared predicates, clock, endian flag, FFI and base/top addresses.

## Expression evaluator: all 16 constructors

Compared `Pan/EvalExact.lean:evalHOLExact` (reached by `evalHOLFinite`) against
`G/cakeml/pancake/semantics/panSem.v:eval`. `EvalFinite.lean` contains the
finite-carrier equations. Evaluation is pure: differing order of independent
failed subexpression tests does not perform effects.

| Constructor | Compared behavior, including rejection cases |
| --- | --- |
| Const | Return a scalar word value unchanged. |
| Var | Local/global selects the corresponding finite map; missing lookup yields none. |
| RStruct | Option-map all fields in order; any failed field yields none, empty fields succeed. |
| RField | Require a record value; return exactly the indexed member if index<length, otherwise none. Lean option indexing matches the guarded Rocq total EL. |
| NStruct | First matching context entry required; ordered field-name lists must match; evaluate all fields; zip expected shapes with resulting shapes and require equality. Output retains names and values in that order. Equal name lists and successful list evaluation supply equal zip lengths. |
| NField | Require a named value and presence of that structure name in context; first matching field lookup, not a new completeness or shape guard. |
| Load | Require well-formed shape, then scalar address; structured memory load, including failure. |
| Load32 | Require scalar address; 4-byte alignment and aligned-cell domain; assemble bytes in state endian order and zero-resize to width64. |
| LoadByte | Require scalar address; aligned-cell domain; extract byte in state endian order and zero-resize. |
| Op | Evaluate all args, require every value scalar; And folds from all-ones, Add/Or/Xor from zero, Sub accepts exactly two args. Empty fold behavior is preserved. Nonword totalization (Lean zero, Rocq ARB) is unreachable behind the scalar guard. |
| Panop | Same scalar/list guards; Mul accepts exactly two words, otherwise none. |
| Cmp | Two scalar operands; original signed/unsigned/equality/test comparisons; return word1 or word0. |
| Shift | Two scalar operands; amount is unsigned natural, not masked. Reject nonzero amount>=width; zero allowed. Lsl/Lsr/Asr/Ror retain word behavior. |
| BaseAddr | Return state base word. |
| TopAddr | Return state top word. |
| BytesInWord | Return n2w(width/8), hence word8 at width64. |

Supporting comparisons: Flapjack `Pancake/WordLang.lean`'s
`wordOpHOL`/`wordShiftHOL`, `Compiler/Encoders/Asm.lean`'s `wordCmpHOL`,
`Pan/ValueHOL.lean`'s scalar predicates, `shapeOfHOLExact`, flatten and primitive;
Galette `wordLang.v`, `asm.v`, `backend_common.v` and `panSem.v`.
AddCarry requires exactly three scalar arguments, interprets **any nonzero**
carry input as one, and returns a two-field record of low result and overflow
word (1 iff unsigned sum>=2^width). No boolean-only carry premise is added.
List evaluators preserve arity/order and short-circuit failure.

## Ordinary memory and structure helpers

Compared `Pan/MemLoadHOL.lean`, relevant definitions in
`Flapjack/Pancake/Semantics/PanSemStateEval.lean`, and
`Flapjack/Pancake/PanLang/Decl.lean` against Galette `panSem.v`, `panLang.v`,
and `HOL/src/n_bit/byte.v`.

| Helper | Compared behavior |
| --- | --- |
| shape_of, flatten | Scalar One/single cell; positional record Comb/concatenated fields; named record Named/name plus flattened field values in list order. |
| shape well-formedness/size | One true/1; Comb conjunction/sum; Named requires first matching context entry and reads stored size, missing size fallback1. No deep context validity guard is silently introduced. |
| mem_load One | Exact address domain membership, then return total memory cell; no extra alignment test. |
| mem_load Comb / list / fields | Load each member at current address, advance by bytes_in_word * n2w(context-sensitive shape size); any failure rejects whole result. Address arithmetic wraps. |
| mem_load Named | Scan to first matching name, then load its fields under the **tail after that entry**. Earlier entries and selected entry are excluded from nested resolution. Missing name fails. Galette dropWhile and Lean recursive scan implement the same operation, including duplicate-name contexts. |
| structured load recursion | Lean decreases (context length, shape size); Galette fuel starts length(context)+1 and decreases for each matched Named. Context strictly shrinks on every such descent, so the added fuel does not bound successful source accesses more tightly. Comb recursion is structural. This argument should be formalized for transport. |
| mem_load_byte / mem_store_byte | Align cell at width64 to 8 bytes; test aligned address domain; endian index is address mod8 or 7-(address mod8); only selected byte changes on store. |
| mem_load_32 / mem_store_32 | Test address mod4=0; check the aligned cell; use four bytes from/into that same cell, with wrapped word addresses and state endian flag. At width64 the four bytes lie within that cell. |
| mem_store / mem_stores | Exact-address domain, functional update; multiword writes advance by word8 after each success and fail as a whole on any missing cell. |
| write_bytearray | Tail recursion first, then head store; a failed head store returns the **original outer memory**, discarding the recursive tail result. Both definitions retain this unusual behavior; it is not a skip-over-unmapped-byte algorithm. |

Byte helpers were inspected as definitions: width64 alignment and byte
replacement are ordinary division/masks modulo 2^64. This review is not a
claim about arbitrary zero or subbyte widths; the original challenge fixes64.

## Program evaluator: all 21 constructors

Compared `Pan/StateExactFiniteMap.lean:evalPanSemRecursiveCallFiniteContext`,
its finite/nonrecursive projection to `Pan/TotalEvalExact.lean`, and
`Pan/{AssignPrimitiveExact,StoreExact,ExtCallExact,TickShMemExact,ShMemExact}.lean`
against `G/cakeml/pancake/semantics/panSem.v:evaluate_body`.
The rows below use the runtime result and state after removing Lean's inert
outer assembly option.

| Constructor | Compared behavior, including state on failure |
| --- | --- |
| Skip | Normal none, unchanged state. |
| Dec | Evaluate initializer; require exact declared shape; update local and run body. Restore this binding from original locals (erase if absent), preserving other post-state fields and result. Failed initializer/shape returns Error and original state. No clock charge. |
| Assign | Evaluate source, require existing selected local/global with equal shape; update it. Missing/invalid value returns Error and original state. |
| Primitive | Evaluate argument list, apply primitive, require valid existing local destination; update local. Every failure retains original state. |
| Store | Scalar destination, arbitrary value flattened; all-cell memory store; update memory only on success, otherwise Error/original state. |
| Store32 | Scalar address/value, low32 source; store32 helper and its alignment/domain failure; only memory changes. |
| StoreByte | Scalar address/value, low8 source; storebyte helper and domain failure; only memory changes. |
| Seq | Run first; clamp returned clock to entry clock even for exceptional result. Only normal none runs second; every other result short-circuits with clock-fixed post-state. |
| If | Scalar condition; zero chooses else, any nonzero then; invalid expression/value gives Error/original state; no clock charge. |
| While | Zero condition exits normally without charging clock. Nonzero at clock0 gives TimeOut with empty locals. Otherwise decrement before body, fix clock against decremented entry; none/Continue repeat, Break becomes normal none, other result propagates. Invalid condition gives Error/original state. |
| Break | Break/unchanged state. |
| Continue | Continue/unchanged state. |
| Call | Full argument/code/clock/result/handler cases are expanded below; no successful-call premise hides failed cases. |
| DecCall | Full cases expanded below, including continuation scope restoration. |
| ExtCall | Four scalar expressions in pointer,length,pointer,length order; read both arrays from ordinary byte memory. Read/eval failure returns Error/original state. Terminal FFI returns FinalFFI with empty locals and old FFI. Returned FFI installs new FFI and writes returned bytes at second pointer. No clock charge. |
| Raise | Evaluate payload, lookup exception shape, exact shape and size<=32; successful Exception clears locals, every failure returns Error/original state. |
| Return | Evaluate payload, size<=32; successful Return clears locals, every failure returns Error/original state. |
| ShMemLoad | Scalar address and already-existing scalar destination required. Op8/16/32/W mean byte count1/2/4/0. Check raw shared address for0, aligned-cell shared address otherwise. Call mappedRead with `[n2w nb]` and little-endian address. Terminal result clears locals; return decodes word_of_bytes and updates destination+FFI only. |
| ShMemStore | Two scalar expressions; same size/address-domain rule. Call mappedWrite with whole word bytes for0, TAKE nb otherwise, then address bytes. Terminal FinalFFI **preserves locals**, unlike ShMemLoad/ExtCall. Return updates FFI only and ignores returned data. |
| Tick | Clock0 gives TimeOut and empty locals; otherwise decrement and normal none. |
| Annot | Normal none, unchanged state, no clock charge. |

### Call and DecCall branches

Both evaluate args before code lookup. `lookupCodeCanonicalHOL` reaches
`Pan/DecCallExact.lean:lookupCodeHOLExact`; Galette reaches `lookup_code`.
Missing function, duplicate parameter names, wrong arity or any shape mismatch
fails. Lean explicitly checks equal lengths plus zipped shapes; Rocq LIST_REL
contains that equal-length condition. Callee locals are fresh empty-map ordered
updates from zipped parameter names/values; caller globals and other fields
are retained. Clock0 returns TimeOut with empty locals. Otherwise both decrement
clock and enter the body with callee locals; body result clock is clamped against
that decremented callee entry.

For **Call**:

* Body none, Break or Continue becomes Error at the clock-fixed **body state**,
  rather than rolling back to caller state.
* Return requires the body's declared return shape. Mismatch gives Error/body
  state. With metadata none it propagates Return and empties locals. With
  metadata some(no destination, _) it completes normally after restoring
  caller locals. With a destination it checks validity against the original
  caller state; success restores caller locals then updates destination,
  failure gives Error/body state.
* Exception with metadata none or no handler propagates with empty locals.
  A nonmatching handler id does the same. A matching handler looks up the
  exception shape in the original caller, checks payload shape and original
  local handler-variable validity; any failure gives Error/body state.
  Success restores caller locals, installs handler variable, and runs the
  handler from the clock-fixed body state. Handler result is not coerced into
  Return or normal completion.
* Other results (Error, TimeOut, FinalFFI) propagate with empty locals.

For **DecCall**:

* Body none, Break, Continue becomes Error/body state.
* Return must match both continuation binding shape and callee return shape.
  Failure gives Error/body state. Success restores caller locals, installs
  returned binding, and evaluates continuation. Restore only that binding
  afterward, from the original caller lookup; retain result and every other
  post-state field. There is no Call-style preexisting-variable requirement
  for this newly declared binding.
* All other body results propagate with empty locals; DecCall has no handler.

### Recursion and clocks

Lean uses well-founded `(state.clock, sizeOf program)` recursion. Galette uses
structural `evaluate_c` with auxiliary fuel `S(N.to_nat clock)`, and separate
same-clock `go` and lower-clock `lower` calls. The auxiliary zero-fuel Error
branch is not an added limit on public `evaluate`: the pinned file proves
`evaluate_c_fuel`, `evaluate_eq_c`, and `evaluate_eqn`, the last giving the
recursive clause equation with public `evaluate` in both positions.
Clock-fixed same-clock continuations have smaller syntax; loops, callees and
handlers/DecCall continuations use a strictly decreased clock. This accounts
for every recursive branch rather than assuming fuel equality from test runs.
These existing Rocq proofs were read; this audit did not compile them anew.

## Declaration and source observational semantics

| Operation | Clause comparison |
| --- | --- |
| decs_stcnames | Empty list succeeds; Name rejects existing name, repeated fields or ill-formed field shape; prepends fields plus computed Comb size under prior context. Decl/Function/ExnDecl skip. Original `Pan/DeclContextExact.lean`, Galette `decs_stcnames`. |
| evaluate_decls | Empty succeeds; Name skips; Decl evaluates under empty locals then shape-checks and updates globals in the original state; Function checks all parameter and return shapes then updates code; ExnDecl requires absent id and well-formed shape then updates eshapes. Every failed guard/expression gives none. |
| semantics_decls | Start structure prepass from empty context; either prepass/evaluation failure is Fail. Otherwise set structures and invoke source semantics. Original `Pan/Semantics.lean`, Galette `semantics_decls`. |
| semantics: failure priority | Evaluate Call None start [] at every natural clock; if any result is outside TimeOut/FinalFFI/Return, choose Fail before checking termination. This includes normal none, Break, Continue, Exception and Error. |
| semantics: termination | Guarded choice of an actual evaluated state/result/outcome; FinalFFI maps to FFI_outcome, Return to Success, recording exactly returned state's FFI events. No bounded-clock or outcome filter is inserted here. |
| semantics: divergence | If no chosen terminating behavior, build prefix LUB of the whole clock-indexed event-trace image. No finite clock cutoff. |

Guarded choice is Lean `holOptionSome` (`Misc/Option.lean`, Classical.choose
under an existence proof) versus Rocq `some` (select under the same existence
predicate). Both select a witness if one exists and none otherwise. They do
not imply equal choices among multiple witnesses. A transport theorem for
actual source behavior must use termination determinism and prefix-chain /
unique-LUB evidence, or specify a compatible choice interpretation; replacing
that obligation by a structural resemblance claim would be incorrect.
`Misc/LprefixLub.lean` and Galette `lprefix_lub.v` have corresponding
pointwise nth choice, unfolding and least-upper-bound definitions. Lazy-list
representations require their extensional nth relation, not equality of record
proof fields across assistants.

## Target evaluator: complete dispatch and helpers

Compared `Target/{State,EncodedBytes,FfiReads,MappedMemory,Evaluate,MachineSem}.lean`
against `G/cakeml/compiler/backend/semantics/targetSem.v`. All 16 machine-config
fields correspond, including three separate indexed interference streams and
MMIO association list. No source-side validity premise is imported into the
public evaluator's quantifiers.

| Case/helper | Clause comparison |
| --- | --- |
| clock0 | TimeOut, original machine and FFI; even at halt/cache/FFI PC. |
| dispatch priority | Program domain minus FFI entries first; then halt, cache-clear, first matching FFI entry; otherwise Error. Halt/cache do not override a program address. |
| encoded guard | Exist an assembly instruction and alignment-block drop offset with offset strictly below encoded length; dropped suffix must be in memory/domain at current PC. Not a decoder-success or full-instruction-only test. Carrier caveat below. |
| ordinary step | Compute next(ms), then answer0 of next interference and shift that stream. Check state_ok at old ms, ms1 and ms2 and unchanged bytes outside program domain from ms to **ms1**, not ms2. Success recurses with k-1 and updated next stream only. Failure retains original ms and FFI. |
| halt | Pointer register zero gives Success, otherwise Resource_limit_hit; retains machine/FFI. No extra state_ok guard. |
| cache-clear | Invoke answer0 on ptr,len,ms, shift only cache stream, recur k-1. No inserted validity/memory guard. |
| FFI selection | find_index returns first match starting0. Name uses total EL, without a new length guard or fallback option. Out-of-range HD uses opaque arbitrary ffiname; it is not the concrete inhabited witness. |
| mappedRead | Require MMIO info; Addr reg+offset wraps; size0 requires address mod(width/8)=0, other sizes no such test. Require shared address and encoded read template. Call FFI with [size] and little-endian address bytes. |
| mappedWrite | Same address/guard rule plus encoded write template; whole word bytes for size0, word_to_bytes_aux(size) otherwise, followed by address bytes. No use of machine endian flag for wire bytes. |
| template helpers | Size1/0/2/4 encode Load8/Load/Load16/Load32 or Store8/Store/Store16/Store32, respectively; any other size False. Return-PC parameter remains unused and polymorphic. |
| external call | Require absence of MMIO info at index; read both arrays through program-domain byte getter, using ptr/len and ptr2/len2. Any missing array gives Error/original state. |
| FFI terminal | Halt(FFI_outcome event), original machine and FFI, no interference answer or stream advance. |
| FFI return | Invoke answer0 of FFI interference on index,new_bytes,old ms; shift only FFI stream; recur with returned FFI and k-1. Returned byte count is checked by call_FFI, not a new evaluator guard. |
| apply_oracle | Answer0 plus shift_seq1; streams advance by exactly one on corresponding successful branch. |
| byte-array read | Length0 succeeds []; otherwise get current byte and recurse at wrapped address+1; any missing byte fails. |
| machine_sem Terminate | Exists finite k, post-machine and FFI with actual Halt outcome and exact final event list. |
| machine_sem Diverge | Every natural k has TimeOut result, and trace satisfies LUB relation of all clock traces; no permission to substitute Error or Halt. |
| machine_sem Fail | Exists clock whose first result is Error. |

`Misc/FindIndex.lean`, `Misc/ListEl.lean` and `Misc/Sptree.lean` were followed
for first-match index, total HD/TL/EL and first-match association lookup;
Galette `find_index`, `EL` and `ALOOKUP` retain those operations.
`readFfiBytearrayHOL` uses `readBytearrayWordHOL`, not a bounded host array or
partial successful-read premise. The target result's tuple reassociation has
no semantic effect.

### Concrete carrier difference in the encoded guard

Original `Flapjack/Compiler/Encoders/Asm.lean:HolInst` has Skip, Const, Arith,
Mem and excludes FP. Galette `asm.v:inst` adds FP; therefore the quantified
assembly carriers in `encodedBytesInMemHOL` and `encoded_bytes_in_mem` are
not literally identical. This was reported immediately to `rocq-main`.

At the fixed native64 configuration this extra case does not add an encoded
byte sequence: Galette `riscv_target.v:riscv_ast` maps `Inst (FP _)` to
`riscv_encode_fail`, exactly `[ADDI(0,0,0)]`; its `Inst Skip` maps to the same
list. Original `Flapjack/Compiler/Encoders/RiscV/Target.lean:riscvAst` maps `.inst .skip` to
`riscvEncodeFail`, the same instruction. Thus any extra FP witness, including
any permitted alignment-drop offset, can be replaced by an original Skip
witness. This is a source-level argument for this configuration, not generic
ASM carrier equivalence. A full guard transport also needs equality of the
encoders for **every common assembly constructor**, not merely decode/step
correctness or one compiler-produced image. That obligation is separate.

### Canonical unspecified choices at this checkpoint

`theories/Target/ReferenceChoices.v` is now present: opaque `theNone` (Qed
witness supplied by ARB), transparent `referenceThe`, successful Some equation.
`Configuration.riscvNext` uses `referenceThe`, preserving the independent
proof-visible failed-THE interface of Lean `holTheNone`. The prior extra
transparent `THE None = ARB` equation is removed at this checkpoint.
The coordinator reported full Dune and interface regressions passing; this
audit read the definitions and did not rerun a build.

The witness selects one permitted equal-choice implementation internally;
it does not prove arbitrary independent Lean choices equal. Similar carrier
relations must interpret original `holArb` compatibly with Rocq `ARB`, including
total missing FFI names and the arbitrary-whole-target floating getter.
The native64 successful-step proofs do not cover arbitrary failed transitions.

## Shared FFI primitive

Compared `Flapjack/FfiHOL.lean:callFFIHOL` with
`G/cakeml/semantics/ffi/ffi.v:call_FFI`:
empty external name returns old state/bytes with no oracle call or event;
otherwise invoke oracle with name, host, configuration, input bytes. A return
with equal byte length updates host and appends exactly one event with zipped
old/new bytes; mismatched length becomes failed final event with original
name/config/input. Oracle terminal outcome is embedded unchanged. Terminal
paths do not append a successful I/O event or return a modified FFI state.
Neither evaluator strengthens the oracle type by demanding same-length returns.
This preserves malformed-oracle behavior, not just well-behaved challenge calls.

## Evidence and residual proof obligations

The clause inventory contains all 21 program and 16 expression constructors,
four declaration constructors, source semantics branches, all target dispatch
branches, and their executable state/memory/FFI helpers. The observed
assembly-carrier difference is documented rather than omitted. Inspection found
no further differing branch result, guard or field update at fixed width64.
The earlier reference audit's broad shared-evaluator **manual comparison** gap
is narrowed by this report; it is not converted into a machine-checked theorem.

Remaining obligations for a formal cross-assistant fidelity claim:

1. Define word/byte/name/value/finite-map/FFI/state relations and prove all
   helper transports, including size/well-formedness and structured-load fuel
   adequacy. Pointwise map comparison is the relevant relation, not enumeration
   order or unrestricted function-state equivalence.
2. Prove evaluator transport by the clock/syntax relation, using Galette's
   public evaluate equation and Lean's inert assembly-marker theorem. Include
   errors, terminal FFI, local restoration and all nonnative target states.
3. Prove original native64 and Galette encoders equal on common assembly
   constructors, then discharge the FP-to-Skip witness replacement for the
   encoded guard. Internal native64 step/encoder-correctness proofs are useful
   but do not state this cross-assistant byte equality.
4. Relate unspecified choices where they are observable; use witness uniqueness
   for terminating behavior and trace-prefix/LUB uniqueness for observational
   source semantics. Do not identify independent constants by a new axiom.
5. The full compiler pass suite, concrete baseline compilation equality,
   baseline certificate, and positive sealed CLI replay remain separately
   owned completion criteria. This review produces none of those artifacts.

Validation is deliberately read-only. The existing reference audit
`--self-test` was rerun against clean locked dependencies; it checks structural
regeneration/constants and four corruption rejections, not evaluator semantic
truth. Constructor counts were independently enumerated from `panLang.v`.
No Rocq/Lean build or new trusted assumptions were introduced.
The coordinator additionally reported byte-for-byte native extraction agreement
with original Bytes000..220/Bitmaps and kernel-checked artifact layout, while
explicitly leaving concrete compilation equality and positive certification
open. Those are separately reported results, not validation performed here.

Reproduce the mechanical checks (they do not automate clause review):

```sh
rtk proxy python3 scripts/audit_reference.py --self-test \
  --references-root /home/zksecurity/cv_compute/rocq-init-e \
  > /tmp/evaluator-audit-reference-checks.json
rtk proxy python3 - <<'PYCODE'
from pathlib import Path
import re
root = Path('/home/zksecurity/cv_compute/rocq-init-e')
text = (root / 'vendor/galette/theories/cakeml/pancake/panLang.v').read_text()
for name, expected in [('exp', 16), ('prog', 21)]:
    body = text.split('Inductive ' + name + ' (', 1)[1].split('\nArguments', 1)[0]
    constructors = re.findall(r'^\| (\w+) :', body, re.M)
    assert len(constructors) == expected
    print(name, len(constructors), constructors)
PYCODE
```

The inherited script's `open_obligations` describes its own earlier
`30ce3e1` review base; it must not be mistaken for a current failed-THE status.
This report's checkpoint discussion records the integrated opaque repair.

### Definition snapshots (SHA256)

These identify the principal inspected dispatcher definitions at the pinned
commits above; they are provenance evidence, not semantic certificates.

| Source file | SHA256 |
| --- | --- |
| `reference/flapjack/Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean` | `0dbfc55ca8cd81f37de2d406b1603f5ccb1bdea947b9ddbfe6988f63c5bb4f43` |
| `reference/flapjack/Flapjack/Pancake/Semantics/PanSem/EvalExact.lean` | `615fb19cd78c0beaa29db84b090ff842dbec6541de2a1f83f8ef0f4dfe8a9620` |
| `reference/flapjack/Flapjack/Pancake/Semantics/PanSem/MemLoadHOL.lean` | `fed3fb573d0db7ea9795e666540e0819b75604059f86205ee6d28cb208ebead0` |
| `reference/flapjack/Flapjack/Pancake/Semantics/PanSem/Semantics.lean` | `5bbbaa757fe60e33c6fd9048a6a4d642a7f4a783c80940dc1cb60b1cb118e5d0` |
| `reference/flapjack/Flapjack/Compiler/Backend/Semantics/TargetSem/Evaluate.lean` | `c8d0766fc13d21275c154289e99d1bb0dc0015bb93337097ab417e999b61abd9` |
| `reference/flapjack/Flapjack/Compiler/Backend/Semantics/TargetSem/MachineSem.lean` | `a6bcff419df99685104bf2521a1f2d1b5ccc59d98338f4a93efd12dd3734c930` |
| `reference/flapjack/Flapjack/FfiHOL.lean` | `607b2b8a3d3e8fed581990409a3ac819729de1539d825a6af8af2ddf49ccf948` |
| `vendor/galette/theories/cakeml/pancake/semantics/panSem.v` | `45bf94f10c9eb02301c146624037ca4f4020bc02585bf0aa5f4416100aaf6fd9` |
| `vendor/galette/theories/cakeml/compiler/backend/semantics/targetSem.v` | `3bc3eb2b52f73766058188a59d73f49c1868274a2ba7cd4a1d79444d50403005` |
| `vendor/galette/theories/cakeml/semantics/ffi/ffi.v` | `c54f58f5bb4d8dc655eca62278fddeb95b6454bd64b3dea40f46cf285a16c00d` |
