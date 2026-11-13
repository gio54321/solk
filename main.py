"""
Check a Lean export file (in the lean4export NDJSON format).

Exit codes, as expected by the Lean Kernel Arena:
    0: all declarations are accepted
    1: some declaration is rejected
    2: declined, the file uses a feature this kernel does not support

With `--skip-unsupported`, the unsupported declarations are skipped instead, together with all
the declarations that depend on them, and the others are still checked. This is useful to test
the kernel on real-world files, which often contain a few nested inductive types.
"""

import sys
import threading

from solk import parser
from solk.environment import Environment
from solk.parser import ParseError, declaration_names
from solk.types import (
    Declaration,
    Definition,
    Expr,
    InductiveBlock,
    Name,
    Opaque,
    Theorem,
)
from solk.utils import KernelError, UnsupportedError, mentions_constant


def declaration_exprs(decl: Declaration) -> list[Expr]:
    """
    The types and values in `decl`.
    """
    if isinstance(decl, InductiveBlock):
        return (
            [t.info.declaration_type for t in decl.types]
            + [c.info.declaration_type for c in decl.constructors]
            + [r.info.declaration_type for r in decl.recursors]
            + [rule.rhs for r in decl.recursors for rule in r.rules]
        )
    if isinstance(decl, (Definition, Theorem, Opaque)):
        return [decl.info.declaration_type, decl.value]
    return [decl.info.declaration_type]


def check(path: str, skip_unsupported: bool) -> int:
    try:
        exported = parser.parse_exported_definitions(path)
        env = Environment()
        if not skip_unsupported:
            env.add_all(exported)
        else:
            skipped: set[Name] = set()
            for decl in exported.declarations:
                try:
                    if any(mentions_constant(e, skipped) for e in declaration_exprs(decl)):
                        raise UnsupportedError("depends on an unsupported declaration")
                    env.add(decl)
                except UnsupportedError:
                    skipped.update(declaration_names(decl))
            if skipped:
                print(f"skipped {len(skipped)} unsupported constants")
    except (KernelError, ParseError) as e:
        print(f"rejected: {e}")
        return 1
    except UnsupportedError as e:
        print(f"declined: {e}")
        return 2
    print("accepted")
    return 0


def main() -> None:
    args = [arg for arg in sys.argv[1:] if arg != "--skip-unsupported"]
    if len(args) != 1:
        print(f"usage: {sys.argv[0]} [--skip-unsupported] <export.ndjson>")
        sys.exit(3)
    skip_unsupported = len(args) < len(sys.argv) - 1

    # the kernel is written recursively: give it a deep stack
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(512 * 1024 * 1024)
    result: list[int] = []
    thread = threading.Thread(target=lambda: result.append(check(args[0], skip_unsupported)))
    thread.start()
    thread.join()
    sys.exit(result[0] if result else 4)


if __name__ == "__main__":
    main()
