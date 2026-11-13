"""
Check a Lean export file (in the lean4export NDJSON format).

Exit codes, as expected by the Lean Kernel Arena:
    0: all declarations are accepted
    1: some declaration is rejected
    2: declined, the file uses a feature this kernel does not support
"""

import sys
import threading

from solk import parser
from solk.environment import Environment
from solk.parser import ParseError
from solk.utils import KernelError, UnsupportedError


def check(path: str) -> int:
    try:
        exported = parser.parse_exported_definitions(path)
        env = Environment()
        env.add_all(exported)
    except (KernelError, ParseError) as e:
        print(f"rejected: {e}")
        return 1
    except UnsupportedError as e:
        print(f"declined: {e}")
        return 2
    print("accepted")
    return 0


def main() -> None:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <export.ndjson>")
        sys.exit(3)

    # the kernel is written recursively: give it a deep stack
    sys.setrecursionlimit(1_000_000)
    threading.stack_size(512 * 1024 * 1024)
    result: list[int] = []
    thread = threading.Thread(target=lambda: result.append(check(sys.argv[1])))
    thread.start()
    thread.join()
    sys.exit(result[0] if result else 4)


if __name__ == "__main__":
    main()
