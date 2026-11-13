# Solk: a Stupidly Obvious Lean Kernel

The goal of this project is to have a Lean kernel which is
- **Stupid**: it does not implement any optimizations, so it's going to be wildly inefficient, however it's
- **Obvious**: from the code you should be able to easily see what's going on.

The one exception to "no optimizations" are natural number literals: like the official kernel, solk
computes `Nat.add`, `Nat.mul`, `Nat.ble`, ... directly on literals (see `solk/literals.py`), since
unfolding them on unary numbers is hopeless even for small numbers. This trusts that these functions
are the ones of `Init.Prelude`, as the official kernel does.

Nested inductive types are intentionally not supported.

## Usage

```
python3 main.py [--skip-unsupported] <export.ndjson>
```

checks a file exported by [lean4export](https://github.com/leanprover/lean4export). It exits with
0 if everything is accepted, 1 if something is rejected and 2 if the file uses an unsupported
feature (a nested inductive type). With `--skip-unsupported`, unsupported declarations are skipped,
together with everything that depends on them, and the rest is still checked.

## Testing

- `tests/lean` contains small Lean files, each with a declaration `test` that must be accepted
  (`Good`) or rejected (`Bad`). Export them with
  `python3 scripts/export_tests.py <path to lean4export>`, then run them with
  `python3 scripts/run_tests.py tests/exports`. The export also includes some theorems of the Lean
  core library, in `tests/exports/init`: run them with `--skip-unsupported` and a long `--timeout`.
- `tests/handcrafted` contains export files written by hand, for what Lean cannot produce:
  `python3 scripts/run_tests.py tests/handcrafted`.
- The tests of the [Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) can be run
  once built in a checkout of the arena (`uv run lka.py build-test`), with
  `python3 scripts/run_tests.py <arena>/_build/tests`.
