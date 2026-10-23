# Exact compiler-computation optimizations

The production compilation certificate now composes separately compiled
computation checkpoints. Each checkpoint proves exact equality with its original
compiler pass; expensive allocator passes use the proved faster implementation. The challenge, submission theorem
statement, literal ROM, source AST and vendored Galette sources are unchanged.
The complete certificate and verifier replay have **not** finished within the
bounded checks. The previous whole-loop IRC experiment exceeded five minutes;
the production path now divides that loop into resumable chunks.

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

`Baseline/CompilationCertificate.v` now uses `ConcreteCertificate`, which
composes `Frontend`, `WordPipeline`, the lower backend checkpoints and `Complete`.
Its proposition is unchanged. No byte hash, additional assumption or
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

## Production checkpoint workflow

All proof sources are under `theories/Compilation` and participate in the ordinary
Dune theory. There is no experimental load path or external object dependency in
the production certificate.

- Six `Frontend*.v` computation files and `Frontend.v` compose source lowering.
- Every one of the 814 word functions has `PassInput`, `PassSSA`, `PassOptimize`
  and a final allocation/output file. Individual passes have opaque equality
  lemmas; subsequent passes use their materialized outputs.
- Functions 0, 57 and 87 additionally split graph construction, forced edges,
  tagging, filtering, heuristic initialization, selection and assignment.
- `IRCChunks.v` proves exact resumable IRC iteration, including errors and early
  termination. Function 87 has 64 files of at most 100 steps followed by a final
  remainder checkpoint. Function 0 exercises the same composition with two
  smaller chunks. The remainder is evaluated, so the chosen chunk count cannot
  truncate the algorithm or weaken the proof.
- `WordPipeline.v` composes all function equalities. Separate files evaluate
  stack lowering, raw calls, stack allocation/removal/naming, sections, target
  encoding and maximum stack depth. `Complete.v` is symbolic composition.
- `ConcreteCertificate.v` compares the resulting bytes and metadata with the
  unchanged literal ROM, then supplies the unchanged baseline theorem.

Generated `.v` sources are checked in. Regeneration preserves unchanged files
and timestamps (the generator is outside the trust base):

```sh
python3 scripts/generate_compilation_checkpoints.py 814
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 60 --budget 600 --keep-going
```

The runner visits checkpoint dependencies first, builds through Dune, records
per-file wall times in `_build/checkpoints/timings.json` and prints the slowest
completed files. Every file and the complete invocation have explicit limits.
With `--keep-going`, failures block their descendants but independent functions
continue. Rerunning reuses successful objects. It does not reseal the verifier.

For a quick complete per-function proof, including chunk composition:

```sh
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 30 --budget 90 theories/Compilation/Word0000.v
```

For a bounded prefix of the larger loop:

```sh
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 45 --budget 180 theories/Compilation/Word0087_Loop0002.v
```

The diagnostic sources still in `experiments/compilation` import these production
objects. The earlier `irc-*.log` and `binary-*.log` files record historical
measurements of the sparse arrays, bulk degree queries and binary lookup; they
do not establish a full verifier runtime. Full production certificate validation
and a verifier run below three hours remain required.

Current split-layout validation: function 0 (including chunked IRC) and function
1 pass complete per-function proofs. Function 87 passes chunks 0–8 (900 loop
iterations); chunk 9 exceeds a 30s cap. Its first chunks take roughly 10–14s,
and chunk 8 took 26.472s. The aggregate production certificate has not yet been
validated. See `checkpoint-layout-status.json`; further bounded runs continue
from those cached objects.
