"""
Build the Lean tests in `tests/lean` and export them to `tests/exports`.

Each file `tests/lean/Tests/{Good,Bad}/<Name>.lean` is one test: the declaration `test` (and
its dependencies) is exported to `tests/exports/{good,bad}/<Name>.ndjson`. Good tests must be
accepted, bad tests rejected (see `scripts/run_tests.py`).

In addition, each theorem of `INIT_THEOREMS` (and its dependencies) is exported from the Lean
core library to `tests/exports/init/good/<name>.ndjson`. These are real-world tests: they
depend on some nested inductive types, so run them with `--skip-unsupported`, and they are slow.

Needs `lake` and a `lean4export` binary built for the toolchain in `tests/lean/lean-toolchain`:

    python3 scripts/export_tests.py <path to lean4export>
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "tests"
LEAN = ROOT / "lean"
EXPORTS = ROOT / "exports"

INIT_THEOREMS = """
    Nat.add_comm Nat.mul_comm Nat.add_assoc Nat.left_distrib Nat.succ_le_succ Nat.div_add_mod
    Nat.mod_lt Nat.gcd_comm Nat.pow_succ Nat.lt_irrefl Nat.sub_add_cancel Nat.le_antisymm
    Nat.mod_two_eq_zero_or_one Nat.shiftLeft_eq Nat.land_comm Nat.testBit_zero Nat.log2_lt
    Nat.decEq Nat.toDigits Nat.repr List.length_append List.reverse_reverse List.map_map
    List.foldl_append Fin.val_add Fin.ext UInt8.toNat_ofNat Char.ofNat_toNat
    Char.isValidChar_of_isValidCharNat String.utf8ByteSize_append String.append_empty String.ext
    String.toList_ofList Bool.and_comm Bool.not_not decide_eq_true Option.some_inj Prod.ext
    Subtype.ext Quot.sound funext propext Classical.em Int.add_comm Int.neg_neg
    Int.emod_emod_of_dvd Array.size_push ByteArray.size_push Nat.lt_wfRel WellFounded.fix_eq
    Acc.inv
""".split()


def export(lean4export: Path, module: str, decl: str, out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as f:
        cmd = ["lake", "env", str(lean4export), module, "--", decl]
        subprocess.run(cmd, cwd=LEAN, stdout=f, check=True)
    print(f"exported {decl} from {module}")


def main() -> None:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <lean4export>")
        sys.exit(1)
    lean4export = Path(sys.argv[1]).resolve()

    subprocess.run(["lake", "build"], cwd=LEAN, check=True)
    for kind in ("Good", "Bad"):
        for source in sorted((LEAN / "Tests" / kind).glob("*.lean")):
            out = EXPORTS / kind.lower() / f"{source.stem}.ndjson"
            export(lean4export, f"Tests.{kind}.{source.stem}", "test", out)
    for theorem in INIT_THEOREMS:
        export(lean4export, "Init", theorem, EXPORTS / "init" / "good" / f"{theorem}.ndjson")


if __name__ == "__main__":
    main()
