"""
Run solk on a directory of exported tests and compare with the expected outcomes.

The expected outcome of `<name>.ndjson` is read from `<name>.stats.json`, as written by the Lean
Kernel Arena (https://github.com/leanprover/lean-kernel-arena), or else from the directory
containing it: `good` tests must be accepted, `bad` tests rejected. So this runs both our own
tests (see `scripts/export_tests.py`)

    python3 scripts/run_tests.py tests/exports

and the arena tests, once built in a checkout of the arena with e.g.
`uv run lka.py build-test 'tutorial'`:

    python3 scripts/run_tests.py <arena>/_build/tests [glob] [--timeout SECONDS]
"""

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

MAIN = Path(__file__).resolve().parent.parent / "main.py"
STATUS = {0: "accepted", 1: "rejected", 2: "declined"}


def run(test: Path, timeout: float) -> tuple[str, str]:
    """
    The status of solk on `test`, and the last line it printed.
    """
    try:
        proc = subprocess.run(
            [sys.executable, str(MAIN), str(test)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return "timeout", ""
    lines = (proc.stdout + proc.stderr).strip().splitlines()
    return STATUS.get(proc.returncode, "error"), lines[-1] if lines else ""


def expected_outcome(test: Path) -> str:
    stats = test.with_suffix(".stats.json")
    if stats.exists():
        return str(json.loads(stats.read_text()).get("outcome", "?"))
    return {"good": "accept", "bad": "reject"}.get(test.parent.name, "?")


def is_correct(outcome: str, status: str) -> bool:
    return (
        (outcome == "accept" and status == "accepted")
        or (outcome == "reject" and status == "rejected")
        or (outcome == "either" and status in ("accepted", "rejected"))
    )


def main() -> None:
    args = argparse.ArgumentParser()
    args.add_argument("dir", type=Path)
    args.add_argument("glob", nargs="?", default="**/*.ndjson")
    args.add_argument("--timeout", type=float, default=60)
    args.add_argument("--jobs", type=int, default=8)
    opts = args.parse_args()

    tests = sorted(t for t in opts.dir.glob(opts.glob) if "work" not in t.parts)
    with ThreadPoolExecutor(opts.jobs) as pool:
        results = list(pool.map(lambda t: run(t, opts.timeout), tests))

    counts: dict[str, int] = {}
    for test, (status, message) in zip(tests, results):
        outcome = expected_outcome(test)
        verdict = "ok" if is_correct(outcome, status) else status
        counts[verdict] = counts.get(verdict, 0) + 1
        if verdict != "ok":
            name = test.relative_to(opts.dir).with_suffix("")
            print(f"{verdict.upper():9} {name} (expected {outcome}): {message[:150]}")
    print(", ".join(f"{k}: {v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
