# rocq-init-e

## Software guest update

The challenge source now uses the software precompile guest from
`flamingoponderado/stateless-pancaketh` commit
`35569814e3fd569fd98cccdf2a9704683d42d2d9`. Its source and literal
AST are pinned in `source/stateless-pancaketh/Guest/`, with init-e's scratch
arena moved to `[0xb0000000, 0xb0bee000)` so that it lies in the compiler's
source-memory domain (`scratch_in_ordinaryDomain`). The guest performs
precompiles in Pancake code; its only external calls are `halt` and `trap`.
The source FFI therefore terminates on every external call, and the old
accelerator implementation has been removed from the Rocq guest model.
The updated initial ROM literals are pinned from init-e commit
`89acaedaa70389a06503a16bdce7b4bdae0cf255` in
`source/init-e-baseline/`. The importer checks each source file and the
native, bitmap, and complete ROM hashes. The accepted certificate described
below belongs to the previous guest; the Rocq compilation equality and
certificate must be rebuilt for this ROM.

Rocq port of [original init-e](https://github.com/flamingoponderado/init-e),
using pinned [Galette](https://github.com/flamingoponderado/galette) and its
proved Pancake `pan_to_target_compile_semantics` theorem.

**The original baseline passed the sealed isolated submission verifier.**
The exact native bytes, bitmaps, stack maximum and dispatch metadata passed
concrete compilation; the unconditional baseline certificate and sanitized ROM
binding passed recursive kernel checking. The accepted ROM is 950,344 bytes with
literal score `infinity`, using only the five existing Galette foundations.
See [accepted result](docs/baseline-positive-verifier-result.json) and
[complete kernel context](docs/baseline-positive-verifier-kernel.log).
Formal correspondence with the Lean decoder and step function remains outstanding.
See [port status](docs/PORT-STATUS.md) for subsequent results and
[final port review](docs/FINAL-PORT-REVIEW.md) for evidence and remaining gates.

## Authority and statement

Original init-e is authoritative. [reference-lock.json](reference-lock.json)
pins original init-e, its exact Flapjack and riscv-zkvm dependencies, and Galette.
Reference submodules are read-only inputs; Galette is pinned and unmodified.
The original reduced RISC-V interpreter remains the public target for arbitrary
admitted ROM submissions. The full-model embedding serves the compiler proof.

The pinned software guest includes the input arena check. The challenge quantifies
over every input with declared gas at most **200,000,000**, retaining the original
128 MiB input arena and 16-byte framing without an extra input-size premise.
Score `infinity` still requires an input-dependent **finite matching Halt**;
timeout or divergence cannot serve as the witness. Submitted ROM and score are
captured as literals and checked against the fixed precompiled certificate type.

## Toolchain and build

Observed toolchain: Rocq 9.3.0, OCaml 5.2.1 and Dune 3.24.2, with
`rocq-stdlib` 9.2.0. Linux, Python 3, Git, RTK and Bubblewrap with working namespace
isolation are required for the verifier. Exact opam package versions and the
fresh-checkout operator workflow are in [SUBMISSIONS.md](docs/SUBMISSIONS.md).

After selecting the reviewed release commit and initializing its submodules:

```sh
rtk proxy git submodule update --init --recursive
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/audit_reference.py --self-test
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/import_baseline.py --check
rtk proxy env PYTHONDONTWRITEBYTECODE=1 python3 scripts/import_baseline_metadata.py --check
rtk proxy opam exec --switch=rocq-init-e -- python3 scripts/check_compilation_checkpoints.py --timeout 60 --budget 600 --keep-going
timeout -k 5 10800 rtk proxy opam exec --switch=rocq-init-e -- dune build -j 1
```

Use the documented opam switch for these commands. The exact compilation proof
uses separately compiled checkpoints; a fresh build can recompute them.
The bounded checkpoint runner resumes completed files and reports slow phases.
See [checkpoint layout and measurements](docs/compilation-speed/README.md). Do not restart an active build or
run competing compiler/kernel/verifier jobs in a shared checkout.
`galette-theories` is the relative symlink to the pinned theory sources, allowing
a single Dune project without modifying Galette. Reference Lean projects are
excluded from the Rocq build. Extracted compiler output is a proposal until its
exact literal equality is proved; a text-parser compilation is not the AST proof.

## Proof and verifier chain

The imported software guest AST defines the fixed source semantics, host framing,
terminal calls and observations. SourceOrder preserves behaviour when moving main
to the front. The reduced encoder proof supplies the actual machine configuration.
The checked bootstrap reaches the native entry for every input, preserving the
shared-memory oracle. Exact native bytes, headers, bitmap words, source memory,
domains and interference establish every field of `pan_installed`.

NativeCompilerCorrectness applies Galette's compiler theorem and removes its
resource-limit relaxation using stack maximum 538 below the actual limit
2,097,104. TargetTotality produces a finite native Halt with the source outcome
and events; the bootstrap clock shift transports it to the original zeroed
initial state. The final certificate source composes this chain with concrete
compilation. The previous baseline passed a coherent build and sealed recursive
kernel verification; the software guest baseline is being checked.
Installation, compiler equality and a native starting state are not added
challenge premises.

The verifier snapshots sanitized ROM/score, candidate sources and sealed trusted
libraries, compiles inside Bubblewrap, compares the exact module interface and
recursively checks the kernel context. Existing 18 security unit tests and four
real negative CLI cases passed. The previous baseline passed positive replay; the software guest replay is pending.
See [submission protocol](docs/SUBMISSIONS.md) for package contents, operator
sealing, negative tests and the positive command.

## Fidelity and trust limits

The allowed foundations are classical excluded middle, constructive indefinite
description, functional extensionality, propositional extensionality and proof
irrelevance; extra axioms and unsafe kernel declarations are rejected. A proof
may use any subset, including none. Sealing records source/object and launcher
hashes, but does not itself verify source/object freshness or attest the entire
external worker/runtime/plugin/Stdlib/OS closure. The operator must provide a
reviewed, kernel-checked build and protect the complete installation.

[REFERENCE-AUDIT.md](docs/REFERENCE-AUDIT.md) and
[EVALUATOR-AUDIT.md](docs/EVALUATOR-AUDIT.md) record original-source comparisons
and reproducible regeneration evidence. Formal Lean-to-Rocq decoder/step and
shared-semantics correspondence remains explicitly open, including observable
unspecified choices and common-constructor encoder equality. Internal Rocq
compiler-target proofs and matching artifact hashes do not close that obligation.
