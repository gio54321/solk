"""
Literals and the built-in arithmetic on natural numbers.

Nat literals are numbers in binary, but `Nat` is a unary inductive type: `Nat.succ (Nat.succ
Nat.zero)` is `2`. Computing `1000 * 1000` by unfolding `Nat.mul` would build a million
`Nat.succ`. Instead, like the official kernel, we compute the common functions on `Nat`
directly on the literals (see `TypeChecker.reduce_nat`). This is sound only because these
functions are the ones defined in `Init.Prelude`, which we trust to compute the same results.
"""

import math
from collections.abc import Callable

from solk.types import App, Const, Expr, Name, NatLiteral, Zero
from solk.utils import KernelError, mk_name

NAT = Const(mk_name("Nat"), ())
NAT_ZERO = Const(mk_name("Nat", "zero"), ())
NAT_SUCC = Const(mk_name("Nat", "succ"), ())
STRING = Const(mk_name("String"), ())
STRING_OF_LIST = Const(mk_name("String", "ofList"), ())
BOOL_TRUE = Const(mk_name("Bool", "true"), ())
BOOL_FALSE = Const(mk_name("Bool", "false"), ())

# The largest exponent (or number of bits for a shift) we agree to compute: the result of
# `2 ^ n` takes `n` bits of memory.
MAX_EXPONENT = 2**24


def nat_pow(base: int, exponent: int) -> int:
    if base > 1 and exponent > MAX_EXPONENT:
        raise KernelError(f"refusing to compute Nat.pow with exponent {exponent}")
    return int(base**exponent)  # `**` on ints may return a float, but not here


def shift_left(n: int, shift: int) -> int:
    if n != 0 and shift > MAX_EXPONENT:
        raise KernelError(f"refusing to compute Nat.shiftLeft by {shift}")
    return n << shift


# The binary functions on `Nat` that are computed on literals, with their semantics. The
# predicates return a Python `bool`, which becomes `Bool.true` or `Bool.false`. Note that on
# `Nat`, subtraction is truncated at 0, and dividing by 0 gives 0.
NAT_BINARY_OPS: dict[Name, Callable[[int, int], int | bool]] = {
    mk_name("Nat", "add"): lambda a, b: a + b,
    mk_name("Nat", "sub"): lambda a, b: max(a - b, 0),
    mk_name("Nat", "mul"): lambda a, b: a * b,
    mk_name("Nat", "div"): lambda a, b: a // b if b != 0 else 0,
    mk_name("Nat", "mod"): lambda a, b: a % b if b != 0 else a,
    mk_name("Nat", "gcd"): math.gcd,
    mk_name("Nat", "pow"): nat_pow,
    mk_name("Nat", "beq"): lambda a, b: a == b,
    mk_name("Nat", "ble"): lambda a, b: a <= b,
    mk_name("Nat", "land"): lambda a, b: a & b,
    mk_name("Nat", "lor"): lambda a, b: a | b,
    mk_name("Nat", "xor"): lambda a, b: a ^ b,
    mk_name("Nat", "shiftLeft"): shift_left,
    mk_name("Nat", "shiftRight"): lambda a, b: a >> b,
}


def nat_value(expr: Expr) -> int | None:
    """
    The number `expr` stands for, if it is a literal or `Nat.zero`.
    """
    if isinstance(expr, NatLiteral):
        return expr.value
    if expr == NAT_ZERO:
        return 0
    return None


def nat_lit_to_constructor(n: int) -> Expr:
    """
    A nat literal as a constructor application: `0` is `Nat.zero`, `n + 1` is `Nat.succ n`.
    """
    if n == 0:
        return NAT_ZERO
    return App(NAT_SUCC, NatLiteral(n - 1))


def nat_predecessor(expr: Expr) -> Expr | None:
    """
    `n` if `expr` is `n + 1`, either as a literal or as `Nat.succ n`.
    """
    if isinstance(expr, NatLiteral) and expr.value > 0:
        return NatLiteral(expr.value - 1)
    if isinstance(expr, App) and expr.fn == NAT_SUCC:
        return expr.arg
    return None


def string_lit_to_constructor(s: str) -> Expr:
    """
    A string literal as `String.ofList` of the list of its characters, e.g. `"ab"` is
    `String.ofList [Char.ofNat 97, Char.ofNat 98]`.
    """
    char = Const(mk_name("Char"), ())
    chars: Expr = App(Const(mk_name("List", "nil"), (Zero(),)), char)
    for c in reversed(s):
        code = App(Const(mk_name("Char", "ofNat"), ()), NatLiteral(ord(c)))
        chars = App(App(App(Const(mk_name("List", "cons"), (Zero(),)), char), code), chars)
    return App(STRING_OF_LIST, chars)

