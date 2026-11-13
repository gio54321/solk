"""
Build the Lean tests in `tests/lean` and export them to `tests/exports`.

Each file `tests/lean/Tests/{Good,Bad}/<Name>.lean` is one test: the declaration `test` (and
its dependencies) is exported to `tests/exports/{good,bad}/<Name>.ndjson`. Good tests must be
accepted, bad tests rejected (see `scripts/run_tests.py`).

Needs `lake` and a `lean4export` binary built for the toolchain in `tests/lean/lean-toolchain`:

    python3 scripts/export_tests.py <path to lean4export>
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "tests"
LEAN = ROOT / "lean"
EXPORTS = ROOT / "exports"


def main() -> None:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <lean4export>")
        sys.exit(1)
    lean4export = Path(sys.argv[1]).resolve()

    subprocess.run(["lake", "build"], cwd=LEAN, check=True)
    for kind in ("Good", "Bad"):
        out_dir = EXPORTS / kind.lower()
        out_dir.mkdir(parents=True, exist_ok=True)
        for source in sorted((LEAN / "Tests" / kind).glob("*.lean")):
            module = f"Tests.{kind}.{source.stem}"
            out = out_dir / f"{source.stem}.ndjson"
            with open(out, "w") as f:
                cmd = ["lake", "env", str(lean4export), module, "--", "test"]
                subprocess.run(cmd, cwd=LEAN, stdout=f, check=True)
            print(f"exported {module}")


if __name__ == "__main__":
    main()
