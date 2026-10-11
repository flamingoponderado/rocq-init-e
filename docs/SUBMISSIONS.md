# Submission protocol (integration in progress)

The verifier has passed real rejection tests. A successful full baseline
package remains required before this protocol is considered ready.

A package directory contains `rom.bin`, `claim.json`, `Solution.v` and optional
Rocq helper sources. Binary/compiled helpers and symlinks are rejected.
`claim.json` contains exactly `{"K":"infinity"}` or a nonnegative JSON integer
in `K`. The ROM admission bound is 1..128 MiB; this is the original code bound,
not a new restriction on challenge inputs. Claims are limited to 1 MiB of JSON.

The verifier generates immutable `SubmissionLiterals.Values` from the bytes
and claim. `Solution.v` can import it and must export:

- `submission : InitE.InitE.SubmissionModel.Submission`;
- `certificate` proving the original fixed certificate for that submission.

The trusted precompiled interface reconstructs submission code/score from the
sanitized literals, retaining only participant dispatch metadata. Certificate
conversion must match this exact reconstructed submission. Changing a local
statement, using different ROM bytes or claiming another score fails the
module interface check.

Notation/grammar changes, ML loading, extraction, redirects, exports and file
loading directives are unsupported in participant sources. Standard proof
commands and imports are compiled inside Bubblewrap with only toolchain,
trusted libraries, protected literals and package files mounted. Network/PID
namespaces are isolated and environment variables are cleared. Generated
literals are mounted read-only during participant compilation. The checker
compiles against read-only candidate objects, then `rocq check` replays all
dependencies. Exactly the five foundation axioms are allowed; type-in-type,
unsafe fixpoints and assumed positivity are rejected.

## Operator preparation

From a reviewed checkout and verified build:

```sh
dune build -j 3
# Independently check the trusted fixed challenge and verifier core.
rocq check -bytecode-compiler yes -silent -o \
  -Q _build/default/galette-theories Galette \
  -Q _build/default/theories InitE InitE.InitE.VerificationCore
python3 scripts/seal_verifier.py
```

The seal records source and compiled-library hashes. Verification never
reseals; changes or unsealed additions invalidate it. Resealing during a run
also invalidates that run.

```sh
python3 verifier/verify.py /path/to/package --output .artifacts/replay-new
```

The verifier reads inputs through regular-file descriptors without following
symlinks in any path component, and checks for concurrent writes. It validates
the copied sources again before invoking Rocq. ROM bytes and the claim are
read once for literal generation. All stages run in a private directory under
`/tmp`; only hash-checked `.vo` snapshots are mounted as challenge libraries.
The main checkout `_build` is never mounted or written by a stage. Logs and
artifacts are copied to the requested output after the sandbox exits, including
on stage failure. Use an operator-owned output parent directory.

The seal is an operator trust anchor, not a signature supplied by a participant.
Keep the checkout, seal, verifier installation, `/usr`, system libraries and
the entire Rocq toolchain prefix inaccessible to participant writes throughout
a run. The seal hashes the Rocq launcher, not every runtime executable, plugin
or standard-library dependency; it cannot authenticate an attacker-controlled
toolchain. Replacing trusted files requires operator review, kernel checking
and resealing. Private snapshots prevent later challenge-library changes from
changing what a verification stage loads.

Kernel summaries must contain exactly one of each expected audit section.
Unknown or repeated sections, contradictory theory flags and extra axioms
fail closed. A proof using a subset of the five foundation axioms, including
no axioms, remains admissible.

Run the fast security regressions with:

```sh
python3 -m unittest discover -s verifier -v
```

Outputs include stage logs, protected generated literals and the final kernel
context. Only a successful complete check produces `VERIFIED` and
`result.json`. The default timeout is 10,800 seconds per stage with a 112 GiB
address-space ceiling. A positive baseline replay is still outstanding.
