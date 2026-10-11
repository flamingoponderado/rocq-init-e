# rocq-init-e

Rocq port of [original init-e](https://github.com/flamingoponderado/init-e),
using [Galette](https://github.com/flamingoponderado/galette) for the Pancake
compiler and its proved `pan_to_target_compile_semantics` theorem.

**Work in progress. There is no verified baseline challenge certificate or
submission acceptance verifier yet.** The intended deliverable is the original
challenge, including arbitrary untrusted ROM submissions, the restricted
RISC-V evaluator, sanitized bytecode and score literals, and kernel checked
certificates against an immutable challenge statement.

## Authority and dependencies

Original init-e is authoritative. `reference-lock.json` pins original init-e,
its exact Flapjack and riscv-zkvm dependencies, and Galette. The HOL4 port is
not the reference for this port. Reference submodules are read-only inputs;
Galette is pinned and unmodified.

The imported guest includes PR25's input arena bounds check. The challenge
retains its declared **200,000,000 gas** premise and 128 MiB input arena,
including its 16-byte framing. No extra input-size premise is introduced.

## Build

Toolchain: Rocq 9.3.0, OCaml 5.2.1, Dune 3.24.2.

```sh
git submodule update --init
python3 scripts/import_guest.py --check
python3 scripts/import_decoder.py --check
dune build -j 3
```

`galette-theories` is a relative symlink to the pinned dependency's theory
sources. It makes both Rocq theories visible to a single Dune project without
modifying Galette. Reference Lean projects are excluded from the Rocq build.
Galette's extracted compiler can be built separately in `vendor/galette`.

## Current implementation

- Literal guest AST reproducibly translated from `Guest/Ast.lean`.
- Finite/infinite score, memory constants, and total declared-gas reader.
- Input framing, startup words, shared-memory handlers, all accelerator calls.
- Fixed Pancake source state and behavior, trace replay and output matching.
- Literal original RV64IM decoder and its outer instruction step equation.
- Kernel checked accelerator known-answer and decoder-boundary regressions.

These modules do not yet constitute a complete challenge certificate.
[Port status](docs/PORT-STATUS.md) lists the remaining work and distinctions
between compilation, translation review, and full verification.
