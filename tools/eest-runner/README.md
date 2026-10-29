# EEST runner

A native runner for the software guest, extracted from
`InitE.Witness.Runner.runInput`. It runs EEST inputs through the Pancake
source semantics without compiling to RISC-V. It is a testing tool, not part of
the challenge proof.

## What is proved and what is trusted

`runInput clock len input` runs the computable evaluator
(`Witness/Evaluator.v`, proved equal to panSem in `Witness/EvaluatorCorrect.v`).
`runInput_halted` shows that a `Halted` report is `sourceBehaviour input`, and
that the reported bytes are `outputByte` of that run. The theorem uses only
the four allowed axioms.

Trusted: Rocq extraction, the OCaml toolchain, and the realizations in
`src/Extract.v`:

* `N` and `positive` as Zarith integers, `nat` as OCaml integers, and `ascii`
  as characters.
* Galette's `fmap` as `src/fmap.ml`: a base function with persistent
  overrides, bucketed by `Hashtbl.hash`. This assumes that keys the Rocq
  decider calls equal hash equally, which holds for the strings and words used.
* `nthN` as an array lookup, `src/nth.ml`.
* `constructive_indefinite_description` (reached only through `select`/`ARB`)
  raises if called.

## Build and run

Zarith is required (`opam install zarith`). The runner is not in the default
build:

```sh
dune build tools/eest-runner/src/eest_runner.exe
```

The command line matches `spike_run`'s: `eest_runner.exe [ELF] INPUT OUTPUT`.
The ELF argument is ignored. `INPUT` is a converted EEST input (an 8-byte
little-endian length, then the payload). `OUTPUT` receives `SPIKE_OUTPUT_LEN`
output bytes (default 256). `EEST_RUNNER_CLOCK` sets the source clock
(default 2^40). Exit codes:

| Code | Meaning |
|---|---|
| 0 | `halt` |
| 3 | `trap` |
| 4 | clock exhausted |
| 5 | evaluation error |
| 6 | another final call |
| 2 | usage or input error |

The status line on stderr gives the clock used and the number of FFI events.

Because it takes `spike_run`'s arguments, init-e's `tools/eest-run.py` can drive
it unchanged:

```sh
SPIKE_RUN=$PWD/_build/default/tools/eest-runner/src/eest_runner.exe \
  python3 ../init-e/tools/eest-run.py none.elf MANIFEST.tsv --jobs 16 --json results.json
```

`eest-run.py` reads its step counts from Spike's log, so it reports no steps
for this runner.

## Results

The witness block for `InitE.Witness.Score` (EEST case 00818) halts with the
expected result in under a second, using 30,975 clock units.

On the 309 cases of init-e's sampled baseline whose labels appear in the full
`tests-zkevm@v21.0.1` manifest:

* 300 cases are `PASS(full)` and 9 are `PASS(malformed)`.
* The output bytes, debug bytes, trap and stage markers all agree with a
  recorded Spike run of the compiled guest.
* The median case takes 2.7 s.

The runner takes about 0.5–1 µs per RISC-V step that Spike counts for the same
block. Cases with large inputs are slower, because panSem appends each FFI
event to the end of the event list.
