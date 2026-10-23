# Exact compiler-computation optimizations

The concrete compilation certificate now evaluates a faster compiler through a
proved equality with the original compiler. The challenge, submission theorem
statement, literal ROM, source AST and vendored Galette sources are unchanged.
The complete certificate and verifier replay have **not** finished within the
bounded checks. IRC selection now uses sparse working arrays and bulk degree
queries; the large complete-selection example still exceeds five minutes.

## Implementation and preservation proof

`theories/Compilation/FastGraph.v` uses a sparse binary map for the outer
adjacency array while building the graph and inserting forced edges. It converts
the result back to the allocator's original state. Neighbour lists keep exactly
their original order. Reads still happen before writes, including for self
edges, and failure cases preserve exactly the same partial state.

Structural sorted insertion also avoids the original accumulator's quadratic
`List.rev`, with a proof of identical list output.

The proof chain is:

- `mk_graph_fast_exact`: exact result and complete allocator-state equality for
  every renaming, clash tree, live-out list and starting state. This theorem is
  closed under the global context: it uses no axioms.
- `extend_graph_fast_exact`: the same preservation guarantee for forced edges.
- `FastAllocation.select_reg_alloc_fast_exact`: exact equality of the allocator,
  including its original heuristics, failure fallback and non-graph algorithms.
- `FastCompiler.compileWithConfigFast_exact`: exact equality of the entire
  compiler for every configuration and source program.
- `baselineCompilationFast_exact`: equality with the challenge's original
  baseline compilation, including native bytes, bitmaps, stack maximum and
  configuration. It uses only foundations already present in the project.

`Baseline/CompilationCertificate.v` rewrites with that last equality before
computing. Its proposition is unchanged. No byte hash, additional assumption or
weakened submission premise substitutes for an exact equality.

## IRC selection

`MapArray.v` proves the exact list-array interface, including bounds failures.
`SparseState.v` represents all five working arrays with sparse maps while
preserving the other seven allocator fields. `SparseIRC.v` mirrors the original
selection algorithm over that state and proves simulation for every operation.
Its `allocate_fast_exact` theorem equates the complete returned result and
allocator state with the original `do_alloc1`, for arbitrary starting states.

Coalescing uses bounded structural recursion with a proof that the bound is
sufficient whenever the original recursion descends. Neighbour ordering, move
priorities, spill choices, failure fallback and iteration bounds are preserved.

`IRCBulk.v` accelerates partitioning of large spill lists. It prepares a sparse
set of low-degree, non-coalesced candidates once per partition. Small lists use
the ordinary sparse-array predicates; states with insufficient array bounds use
the original operation, preserving failures. Ordered partition results are
identical. No new challenge premise or allocator well-formedness assumption is
required.

`IRCSelection.v` provides both the exact replacement and initialization/loop
checkpoint equations. `FastAllocation.v` now calls this replacement, so the
already proved full-compiler equality carries the change through to the
certificate. The source ROM and challenge statement remain unchanged.

Measured on the same function-87 state (6,420 nodes, 6,417 allocation candidates):

| Measurement | Original | Sparse working arrays |
| --- | ---: | ---: |
| Heuristic initialization computation | >60s | 14.744s before bulk tuning |
| Initialization equality checking | not completed | 6.764s before bulk tuning |
| First three selection steps | 9.220s | 0.530s before bulk tuning |
| First thirty selection steps | not measured | 4.205s before bulk tuning; 2.647s with bulk queries |

The three-step comparison is about 17 times faster. Both implementations produce
the same worklist traces; the formal theorem additionally preserves every
allocator field, not just those observations. These are phase measurements, not
an end-to-end verifier benchmark.

The complete optimized selection, observed only through its final stack length
to avoid a large state read-back, **did not finish within 300 seconds**. Its total
runtime is unknown. The pure worklist/heuristic algorithm still does substantial
work; no full certificate or verifier replay has completed.

The new modules, the allocator integration and the full compiler equality built
successfully after adopting the remote Galette stack-depth-cache update. Each
new module and the integrated compiler passed a separate targeted `rocq check
-norec` invocation. Dependencies were admitted for these checks, so this is not
a completed recursive verifier replay. The allocator equality uses functional
extensionality already present in the project; the full compiler equality uses
only the existing foundations. See `irc-assumptions.log` and `irc-results.json`.

## Earlier graph-only validation and measurements

On the current guest and local Rocq 9.3.0 toolchain:

- Dune built all four new production modules successfully.
- Each module passed a separate `rocq check -norec` invocation. Dependencies were
  admitted for these targeted checks; this was not a full recursive verifier
  replay.
- The split computation/equality proofs for small function 0 passed.
- Function 87's graph contains 6,420 allocator nodes and an 11,889-node clash
  tree. Original `mk_graph` alone exceeded 60 seconds.
- The sparse graph builder completed in 14.531s, followed by 7.243s to check its
  equality (about 22 seconds total). A subsequent run with structural sorted
  insertion took 22.942s including loading, computation and proof checking.
- The remaining tagging and move-filter phases take roughly 12 and 15 seconds.
  IRC selection (`do_alloc1`) still exceeds a separate 60-second limit.
- A 60-second Dune attempt at the complete concrete certificate timed out.
  **No end-to-end verifier speedup or completed submission replay is claimed.**

These measurements describe the earlier graph-only version. The IRC changes
and their remaining complete-selection timeout are described above.

Native evaluation is disabled in this toolchain and falls back to the VM.
Measurements, assumptions and selected timing logs are recorded here. The
existing user `build.log` was not modified.

## Reproduce

The installed switch here is `galette`; select the project's appropriate switch
on another machine. Production proof build:

```sh
timeout -k 5 180 opam exec --switch=galette -- dune build -j 1 \
  theories/Compilation/FastCompiler.vo
```

A targeted independent kernel check, without recursively rechecking dependencies:

```sh
timeout -k 5 20 opam exec --switch=galette -- rocq check \
  -bytecode-compiler yes -silent \
  -Q _build/default/galette-theories Galette \
  -Q _build/default/theories InitE \
  -norec InitE.Compilation.FastCompiler
```

### Resumable computation experiment

The original Lean-inspired stage experiment remains in
`experiments/compilation/`, outside Dune's enabled directories. Its frontend's
six passes and equality proofs compile in about 35 seconds and produce 814
word-language functions. Before the graph optimization, function proofs 0–86
passed, with most small functions taking roughly 0.5–1.5 seconds each. The
full-stage aggregate and experimental final certificate remain unvalidated.

```sh
python3 scripts/generate_compilation_checkpoints.py 814
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 60 --budget 180
```

The runner uses already-built trusted dependencies, compiles sequentially, and
limits each file and the entire invocation. It reuses successful objects and
invalidates them when sources or imported libraries change. Timings and logs go
to `_build/checkpoints/`. Production modules are built by Dune; generated function proofs are compiled
under `.artifacts/`, so the two build methods do not create conflicting objects.
Timeouts terminate the entire compilation process group, including Dune children.

Exit 2 indicates that the total budget expired between files; exit 1 indicates a
compiler error or a timeout during a file. Rerun to resume. Function 87 is split
through graph construction, forced edges, tagging, filtering, selection and
assignment; function 0 provides a small smoke case for the same proof wiring.

The function count is specific to this guest. After changing it, query
`List.length Frontend.words` and regenerate. The aggregate's exact `inputs_eq`
also prevents an incorrect count from silently truncating an accepted proof.

### Reproduce the IRC measurements

After building the production proof modules and generating checkpoints, build
only the frontend, parameters and function-87 initialization (without starting
its whole loop):

```sh
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 60 --budget 180 \
  experiments/compilation/Frontend.v experiments/compilation/CompilerConfig.v \
  .artifacts/checkpoints/Word0087_0[012]*.v \
  .artifacts/checkpoints/Word0087_03aHeuristics.v
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 30 --budget 30 experiments/compilation/IRCMeasurements.v
```

For the complete selection use an explicit longer bound:

```sh
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 300 --budget 300 experiments/compilation/IRCComplete.v
```

The experimental parameters are constructed directly from the same pure backend
configuration as `BaselineCompiler`, so profiling does not need to load its
machine-semantics proof bridge. The aggregate proof still checks against the
original baseline configuration.

## Binary lookup

`FastLookup.binary_lookup` traverses the binary digits of `N.succ_pos k`
instead of repeatedly computing parity, subtraction and division at each tree
node. `binary_lookup_exact` proves equality with Galette lookup for every key,
value type and tree, including absent keys. It is closed under the global
context. Sparse graph reads, working-array reads and bulk eligibility queries
use it; their specifications still use the original lookup. No vendored source
or challenge definition changes.

On the same function-87 checkpoint, graph evaluation took 8.206s and its proof
1.311s (9.816s for the file), versus roughly 23s previously. Heuristic
initialization took 8.382s plus 0.423s for its proof. Three sparse IRC steps took
0.108s and thirty took 0.840s, versus 2.647s for thirty with the preceding bulk
query implementation. The observed worklist traces match the earlier run.
These are local phase measurements, not a whole-verifier timing.

The isolated 6,420-key lookup sweep returned 20,604,990 with both implementations:
arithmetic lookup took 0.055–0.058s and binary lookup 0.002–0.003s. Reproduce with
`LookupMeasurements.v` using the checkpoint runner. Logs and measurements are
in `binary-*.log` and `binary-results.json`.

The full compiler equivalence proof builds, targeted kernel checks pass, and
function 0 passes the complete generated compilation proof through assignment
and extraction. The optimization introduces no additional axioms.

The complete function-87 selection still exceeded a 120s cap after this change;
see `binary-complete-timeout.log`. This does not establish an improvement over
the previous 300s timeout, since neither run completed.
