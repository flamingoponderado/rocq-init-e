# Exact graph-construction optimization

The concrete compilation certificate now evaluates a faster compiler through a
proved equality with the original compiler. The challenge, submission theorem
statement, literal ROM, source AST and vendored Galette sources are unchanged.
The complete certificate and verifier replay have **not** finished within the
bounded checks; there is still a separate IRC-selection bottleneck.

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

## Bounded validation and measurements

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

The next performance target is IRC selection and its remaining list-backed
allocator arrays. The graph-construction improvement is already integrated;
changing that phase again alone will not remove the newly isolated bottleneck.

Native evaluation is disabled in this toolchain and falls back to the VM.
Measurements, assumptions and selected timing logs are recorded here. The
existing user `build.log` was not modified.

## Reproduce

The installed switch here is `galette`; select the project's appropriate switch
on another machine. Production proof build:

```sh
timeout -k 5 60 opam exec --switch=galette -- dune build -j 1 \
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
