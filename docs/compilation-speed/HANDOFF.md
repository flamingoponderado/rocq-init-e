# Agent handoff — 2026-10-23

Continue from `2e09ad8` on branch
`update-software-guest-no-precompile-accelerator` in `rocq-init-e`.
Sibling `init-e` is the Lean reference only; do not edit it.

## Objective and constraints

Split computation into independently compiled files, optimize the slowest
checkpoints, and get a complete verifier replay below three hours. Keep the
challenge, submission theorem statement and literal submitted RISC-V code
unchanged. Exact compilation equality is required, not a hash/count substitute.
Use explicit timeouts for every build/check. Commit and push improvements.
Do not modify the user's untracked `build.log` or vendored Galette sources.

## Commits and repository state

- `653d753`: exact sparse graph construction (pushed previously).
- `2d18697`: sparse working arrays, IRC simulation and bulk spill queries
  (pushed previously).
- `5aeaa4a`: exact binary trie lookup in graph/array/bulk query paths.
- `2e09ad8`: production compilation checkpoint layout and resumable IRC chunks.
- The latter two commits were not pushed: GitHub DNS resolution failed on every
  attempt (`Could not resolve host: github.com`). Retry push once networking works.
- Galette is pinned at gitlink `52220d8e7efa464a0fa04c8511593c907652905f`.
  This includes the remote's cached stack-depth graph change.
- The configured GPG key is expired. Use `git commit --no-gpg-sign`; do not change
  repository/global signing configuration.
- No build or checker process remains running at handoff.

## Current proof architecture

Production sources are in `theories/Compilation`, using the ordinary Dune theory
`InitE.Compilation`. There are 3,386 compilation sources, including 3,356 generated
word checkpoint sources. The generator is outside the trust base; checked-in
`.v` files contain the proofs.

- Six frontend computation files and `Frontend.v` compose source lowering.
- All 814 functions have `WordXXXX_PassInput`, `PassSSA`, `PassOptimize` and
  `WordXXXX.v`. Each pass has a materialized result and opaque equality lemma.
- Functions 0, 57 and 87 additionally split graph construction, forced edges,
  tagging, filtering, heuristic initialization, selection and assignment.
- `IRCChunks.v` proves an exact resumable loop, preserving errors and early
  termination. Function 87 has 64 files of 100 steps and a final residual loop;
  function 0 tests two chunks of two steps. The residual loop is evaluated, so
  a chunk-count mistake cannot silently truncate the accepted computation.
- `WordPipeline.v` composes all per-function equalities. Lower backend files
  split stack lowering, raw calls, allocation/removal/naming, sections, target
  encoding and maximum stack depth. `Complete.v` is symbolic composition.
- `ConcreteCertificate.v` compares actual bytes/metadata against the unchanged
  literals. `Baseline/CompilationCertificate.v` now delegates to this theorem;
  its statement is unchanged. It no longer runs whole-compiler `vm_compute`.
- The aggregate production certificate has NOT yet been validated. Its templates
  were formerly experimental and may need proof-wiring fixes once dependencies
  finish. Do not report a completed verifier run.
- `Local Opaque compileWithConfig` prevents accidental closed full-compiler
  evaluation during proof conversion; retain this in `Complete.v`/`FastCompiler.v`.

## Validation and immediate bottleneck

- All generic fast compiler equivalence proofs previously built and passed
  targeted independent kernel checks. They preserve exact bytes and metadata.
- Binary lookup's equality and sparse graph equality are closed under the global
  context. The full compiler uses only the project's existing foundations.
- Production `Word0000.v` and `Word0001.v` complete per-function proofs pass.
  Function 0 includes chunk composition, allocation, assignment and extraction.
- Separate `rocq check -norec` checks of `IRCChunks` and `Word0000` passed.
  `chunk_resume` is closed under the global context; `checkpoint_resume` uses
  the already-present dependent functional extensionality through simulation.
- Function 87 passes frontend/word passes, all initialization, and loop chunks
  `Word0087_Loop0000` through `Loop0008`: 900 iterations.
- First chunks take about 10–14s per file; chunk 8 took 26.472s.
  `Word0087_Loop0009` exceeded a 30s cap. This is the next concrete bottleneck.
- After chunk 8: 5,517 iterations remain; available moves = 0, spill list = 5,112.
  Spill selection is now the likely hotspot.
- A combined targeted kernel check including the large chunk timed out at 45s;
  do not claim kernel validation of that large chunk. Use separate checks.
- Historical complete selection experiments exceeded 300s (before binary lookup)
  and 120s (after it). Neither produced a result; no full speedup can be inferred.
- Isolated lookup sweep: 6,420 keys, identical sum 20,604,990; original ~0.056s,
  binary ~0.002–0.003s. Earlier graph file ~23s, binary ~9.8s; thirty sparse
  steps fell from 2.647s to 0.840s. These are local measurements only.

## How to resume

Installed switch here is `galette` (Rocq 9.3.0, Dune 3.24.2). The checkpoint runner
visits dependencies first and builds one file through Dune at a time. It records
wall times/logs under `_build/checkpoints/`, including `timings.json`, and kills
whole process groups on timeout. Completed objects are reusable.

```sh
# Regeneration preserves unchanged contents and timestamps.
python3 scripts/generate_compilation_checkpoints.py 814

# Resume the large function, allowing more time for the next spill chunk.
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 60 --budget 600 theories/Compilation/Word0087.v

# Profile all independent functions, skipping descendants of failures.
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 60 --budget 600 --keep-going

# A small complete smoke case.
opam exec --switch=galette -- python3 scripts/check_compilation_checkpoints.py \
  --timeout 30 --budget 90 theories/Compilation/Word0000.v

# A targeted kernel check; use ONE module per invocation.
timeout -k 5 30 opam exec --switch=galette -- rocq check \
  -bytecode-compiler yes -silent \
  -Q _build/default/galette-theories Galette \
  -Q _build/default/theories InitE -norec InitE.Compilation.IRCChunks
```

Do not map the old `.artifacts/checkpoints` or `experiments/compilation` directories
as `InitE.Compilation`: stale `.vo` files there conflict with production CRCs.
Diagnostic `.v` sources remaining in experiments import production Dune objects.
Do not run competing Dune/compiler/kernel jobs. Increase bounds only after the
file granularity makes the measured work meaningful.

## Optimization leads (not yet implemented)

1. `SparseIRC.st_ex_list_MIN_cost` and `do_spill` still use original arithmetic
   `reg_alloc.lookup_any` for every spill-cost lookup. Replace via a local proved
   binary lookup alias; `FastLookup.binary_lookup_exact` already exists.
   Adapt `solve_sim` or its MIN-cost/do-spill proofs to rewrite the alias exactly.
   No edits were started for this optimization.
2. Fuse degree/cost lookup scans, cache eligibility incrementally, or improve
   repeated membership checks in `bg_ok` and `revive_moves`, preserving ordered
   outputs and tie-breaking. Measure the spill checkpoint first.
3. Current chunks pack/unpack sparse arrays at every boundary. Persistent sparse
   chunk state could reduce this overhead but needs an exact composition proof.
4. After all functions pass, validate `WordPipeline`, backend checkpoints,
   `Complete`, literal comparison and final submission theorem. Fix any symbolic
   proof wiring without changing the challenge or literal outputs.
5. Run recursive kernel verification and sealed isolated verifier on Linux.
   This checkout is macOS and has no `bwrap`, so do not claim a complete isolated
   replay from local compilation alone. Do not reseal unvalidated sources.

Additional historical measurements and assumptions are in this directory.
The three-hour target remains unestablished.
