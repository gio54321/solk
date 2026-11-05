from typing import Any
from yalk.types import (
    Anon, App, Axiom, BVar, Const, Declaration, DeclarationInfo, Definition,
    Expr, FVar, Forall, IMax, InductiveBlock, Lambda, Let, Level, Max, MData,
    Name, NatLiteral, Opaque, Param, Projection, Quot, Sort, StringLiteral,
    StrName, Succ, Theorem, Zero,
)

INDENT = "  "


def pp_name(name: Name) -> str:
    parts: list[str] = []
    while not isinstance(name, Anon):
        parts.append(name.name if isinstance(name, StrName) else str(name.name))
        name = name.pre
    return ".".join(reversed(parts)) if parts else "[anonymous]"


def pp_names(names: tuple[Name, ...]) -> str:
    return "[" + ", ".join(pp_name(n) for n in names) + "]"


def pp_level(level: Level) -> str:
    if isinstance(level, Zero):
        return "0"
    if isinstance(level, Succ):
        return f"succ {_level_arg(level.pred)}"
    if isinstance(level, Max):
        return f"max {_level_arg(level.left)} {_level_arg(level.right)}"
    if isinstance(level, IMax):
        return f"imax {_level_arg(level.left)} {_level_arg(level.right)}"
    return pp_name(level.name)


def _level_arg(level: Level) -> str:
    s = pp_level(level)
    return s if isinstance(level, (Zero, Param)) else f"({s})"


def pp_expr(e: Expr, ctx: tuple[str, ...] = ()) -> str:
    if isinstance(e, BVar):
        if e.index < len(ctx):
            return f"(#{e.index}-->{ctx[-1 - e.index]})"
        return f"#{e.index}"  # loose: not bound in this expression
    if isinstance(e, FVar):
        return e.name
    if isinstance(e, Const):
        us = ", ".join(pp_level(u) for u in e.universes)
        return f"{pp_name(e.name)}.{{{us}}}"
    if isinstance(e, Sort):
        return f"Sort {_level_arg(e.level)}"
    if isinstance(e, App):
        return f"{_expr_arg(e.fn, ctx)} {_expr_arg(e.arg, ctx)}"
    if isinstance(e, (Lambda, Forall)):
        var = pp_name(e.var)
        binder = f"({var} : {pp_expr(e.binder_type, ctx)})"
        body = pp_expr(e.body, ctx + (var,))
        if isinstance(e, Lambda):
            return f"fun {binder} => {body}"
        return f"forall {binder}, {body}"
    if isinstance(e, Let):
        var = pp_name(e.var)
        return (f"let ({var} : {pp_expr(e.binder_type, ctx)}) := {pp_expr(e.value, ctx)}"
                f" [nondep={e.nondep}]; {pp_expr(e.body, ctx + (var,))}")
    if isinstance(e, Projection):
        return f"proj {pp_name(e.type_name)} {e.index} {_expr_arg(e.struct, ctx)}"
    if isinstance(e, NatLiteral):
        return str(e.value)
    if isinstance(e, StringLiteral):
        return repr(e.value)
    if isinstance(e, MData):
        return f"mdata {e.data} {_expr_arg(e.expr, ctx)}"
    raise TypeError(f"not an expression: {e!r}")


def _expr_arg(e: Expr, ctx: tuple[str, ...]) -> str:
    s = pp_expr(e, ctx)
    atom = isinstance(e, (BVar, FVar, Const, NatLiteral, StringLiteral))
    return s if atom else f"({s})"


def _field(lines: list[str], key: str, value: Any, depth: int) -> None:
    lines.append(f"{INDENT * depth}{key}: {value}")


def _expr_field(lines: list[str], key: str, e: Expr, depth: int) -> None:
    _field(lines, key, pp_expr(e), depth)


def _info(lines: list[str], kind: str, info: DeclarationInfo, depth: int) -> None:
    lines.append(f"{INDENT * depth}{kind} {pp_name(info.name)}")
    _field(lines, "levelParams", pp_names(info.level_params), depth + 1)
    _expr_field(lines, "type", info.declaration_type, depth + 1)


def pp_declaration(decl: Declaration) -> str:
    lines: list[str] = []
    if isinstance(decl, Axiom):
        _info(lines, "axiom", decl.info, 0)
        _field(lines, "isUnsafe", decl.is_unsafe, 1)
    elif isinstance(decl, Definition):
        _info(lines, "def", decl.info, 0)
        _expr_field(lines, "value", decl.value, 1)
        _field(lines, "hints", decl.hints, 1)
        _field(lines, "safety", decl.safety, 1)
        _field(lines, "all", pp_names(decl.all_names), 1)
    elif isinstance(decl, Theorem):
        _info(lines, "theorem", decl.info, 0)
        _expr_field(lines, "value", decl.value, 1)
        _field(lines, "all", pp_names(decl.all_names), 1)
    elif isinstance(decl, Opaque):
        _info(lines, "opaque", decl.info, 0)
        _expr_field(lines, "value", decl.value, 1)
        _field(lines, "isUnsafe", decl.is_unsafe, 1)
        _field(lines, "all", pp_names(decl.all_names), 1)
    elif isinstance(decl, Quot):
        _info(lines, "quot", decl.info, 0)
        _field(lines, "kind", decl.kind, 1)
    elif isinstance(decl, InductiveBlock):
        lines.append("inductive block")
        for t in decl.types:
            _info(lines, "inductive", t.info, 1)
            _field(lines, "numParams", t.num_params, 2)
            _field(lines, "numIndices", t.num_indices, 2)
            _field(lines, "all", pp_names(t.all_inductive_names), 2)
            _field(lines, "ctors", pp_names(t.constructor_names), 2)
            _field(lines, "numNested", t.num_nested, 2)
            _field(lines, "isRec", t.is_recursive, 2)
            _field(lines, "isUnsafe", t.is_unsafe, 2)
            _field(lines, "isReflexive", t.is_reflexive, 2)
        for c in decl.constructors:
            _info(lines, "ctor", c.info, 1)
            _field(lines, "induct", pp_name(c.inductive_name), 2)
            _field(lines, "cidx", c.constructor_index, 2)
            _field(lines, "numParams", c.num_params, 2)
            _field(lines, "numFields", c.num_fields, 2)
            _field(lines, "isUnsafe", c.is_unsafe, 2)
        for r in decl.recursors:
            _info(lines, "rec", r.info, 1)
            _field(lines, "all", pp_names(r.all_inductive_names), 2)
            _field(lines, "numParams", r.num_params, 2)
            _field(lines, "numIndices", r.num_indices, 2)
            _field(lines, "numMotives", r.num_motives, 2)
            _field(lines, "numMinors", r.num_minors, 2)
            _field(lines, "k", r.is_k, 2)
            _field(lines, "isUnsafe", r.is_unsafe, 2)
            lines.append(f"{INDENT * 2}rules:")
            for rule in r.rules:
                lines.append(f"{INDENT * 3}rule {pp_name(rule.constructor_name)}")
                _field(lines, "nfields", rule.num_fields, 4)
                _expr_field(lines, "rhs", rule.rhs, 4)
    else:
        raise TypeError(f"not a declaration: {decl!r}")
    return "\n".join(lines)
