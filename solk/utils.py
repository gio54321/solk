from collections.abc import Collection

from solk.levels import instantiate_level
from solk.types import (
    Anon,
    App,
    BVar,
    Const,
    Expr,
    Forall,
    FVar,
    Lambda,
    Let,
    Level,
    MData,
    Name,
    Projection,
    Sort,
    StrName,
)


class KernelError(Exception):
    pass


class UnsupportedError(Exception):
    """
    A declaration this kernel intentionally does not handle, such as a nested inductive type.
    It is neither accepted nor rejected.
    """


def instantiate(expr: Expr, arg: Expr, offset: int = 0) -> Expr:
    """
    Instantiate the bound variable at the current offset with the given argument `arg`.
    By default offset is 0, so the bound variable immediately "above" is instantiated.
    """
    match expr:
        case BVar(index):
            return arg if index == offset else expr
        case App(fn, arg_inner):
            return App(
                instantiate(fn, arg, offset), instantiate(arg_inner, arg, offset)
            )
        case Lambda(var, binder_type, binder_info, body):
            return Lambda(
                var,
                instantiate(binder_type, arg, offset),
                binder_info,
                instantiate(body, arg, offset + 1),
            )
        case Forall(var, binder_type, binder_info, body):
            return Forall(
                var,
                instantiate(binder_type, arg, offset),
                binder_info,
                instantiate(body, arg, offset + 1),
            )
        case Let(var, binder_type, value, body, nondep):
            return Let(
                var,
                instantiate(binder_type, arg, offset),
                instantiate(value, arg, offset),
                instantiate(body, arg, offset + 1),
                nondep,
            )
        case Projection(type_name=type_name, index=index, struct=struct):
            return Projection(type_name, index, instantiate(struct, arg, offset))
        case _:
            return expr


def abstract(expr: Expr, fvar: FVar, offset: int = 0) -> Expr:
    """
    Abstract the free variable `fvar` from the expression `expr` with the correct De Bruijn index.
    """
    match expr:
        case FVar(name):
            return BVar(offset) if name == fvar.name else expr
        case App(fn, arg_inner):
            return App(abstract(fn, fvar, offset), abstract(arg_inner, fvar, offset))
        case Lambda(var, binder_type, binder_info, body):
            return Lambda(
                var,
                abstract(binder_type, fvar, offset),
                binder_info,
                abstract(body, fvar, offset + 1),
            )
        case Forall(var, binder_type, binder_info, body):
            return Forall(
                var,
                abstract(binder_type, fvar, offset),
                binder_info,
                abstract(body, fvar, offset + 1),
            )
        case Let(var, binder_type, value, body, nondep):
            return Let(
                var,
                abstract(binder_type, fvar, offset),
                abstract(value, fvar, offset),
                abstract(body, fvar, offset + 1),
                nondep,
            )
        case Projection(type_name=type_name, index=index, struct=struct):
            return Projection(type_name, index, abstract(struct, fvar, offset))
        case _:
            return expr


def instantiate_universe_parameters(
    expr: Expr, parameters: tuple[Name, ...], universes: tuple[Level, ...]
) -> Expr:
    """
    Instantiate universe parameters of a declaration type with the given concrete universe levels
    """
    match expr:
        case Const(name=name, universes=input_universes):
            output_universes = []
            for universe in input_universes:
                output_universes.append(
                    instantiate_level(
                        universe, parameters, universes
                    )
                )
            return Const(name, tuple(output_universes))
        case Sort(level=level):
            return Sort(
                instantiate_level(level, parameters, universes)
            )
        case App(fn=fn, arg=arg):
            return App(
                instantiate_universe_parameters(fn, parameters, universes),
                instantiate_universe_parameters(arg, parameters, universes),
            )
        case Lambda(
            var=var, binder_type=binder_type, binder_info=binder_info, body=body
        ):
            return Lambda(
                var,
                instantiate_universe_parameters(binder_type, parameters, universes),
                binder_info,
                instantiate_universe_parameters(body, parameters, universes),
            )
        case Forall(
            var=var, binder_type=binder_type, binder_info=binder_info, body=body
        ):
            return Forall(
                var,
                instantiate_universe_parameters(binder_type, parameters, universes),
                binder_info,
                instantiate_universe_parameters(body, parameters, universes),
            )
        case Let(
            var=var, binder_type=binder_type, value=value, body=body, nondep=nondep
        ):
            return Let(
                var,
                instantiate_universe_parameters(binder_type, parameters, universes),
                instantiate_universe_parameters(value, parameters, universes),
                instantiate_universe_parameters(body, parameters, universes),
                nondep,
            )
        case Projection(type_name=type_name, index=index, struct=struct):
            return Projection(
                type_name,
                index,
                instantiate_universe_parameters(struct, parameters, universes),
            )
        case _:
            return expr


def has_free_variables(expr: Expr) -> bool:
    match expr:
        case FVar():
            return True
        case App(fn=fn, arg=arg):
            return has_free_variables(fn) or has_free_variables(arg)
        case Lambda(binder_type=binder_type, body=body):
            return has_free_variables(binder_type) or has_free_variables(body)
        case Forall(binder_type=binder_type, body=body):
            return has_free_variables(binder_type) or has_free_variables(body)
        case Let(binder_type=binder_type, value=value, body=body):
            return (
                has_free_variables(binder_type)
                or has_free_variables(value)
                or has_free_variables(body)
            )
        case Projection(struct=struct):
            return has_free_variables(struct)
        case _:
            return False


def get_head(expr: Expr) -> Expr:
    """
    The head `f` of the application `f a1 ... an`.
    """
    return get_head(expr.fn) if isinstance(expr, App) else expr


def get_num_args(expr: Expr) -> int:
    """
    The number `n` of arguments of the application `f a1 ... an`.
    """
    return 1 + get_num_args(expr.fn) if isinstance(expr, App) else 0


def get_fn(expr: Expr, n: int) -> Expr:
    """
    `f a1 ... a(k-n)`, i.e. the application `f a1 ... ak` without its last `n` arguments.
    """
    if n == 0:
        return expr
    assert isinstance(expr, App)
    return get_fn(expr.fn, n - 1)


def replace_fn(expr: Expr, n: int, new: Expr) -> Expr:
    """
    `new a(k-n+1) ... ak`, i.e. the application `f a1 ... ak` keeping only its last `n` arguments,
    and applying `new` to them instead. With `n = k`, this replaces the head `f` with `new`.
    """
    if n == 0:
        return new
    assert isinstance(expr, App)
    return App(replace_fn(expr.fn, n - 1, new), expr.arg)


def has_loose_bvar(expr: Expr, index: int = 0) -> bool:
    """
    True iff the bound variable `index`, bound by some binder outside of `expr`, occurs in `expr`.
    """
    match expr:
        case BVar(i):
            return i == index
        case App(fn, arg):
            return has_loose_bvar(fn, index) or has_loose_bvar(arg, index)
        case Lambda(_, binder_type, _, body) | Forall(_, binder_type, _, body):
            return has_loose_bvar(binder_type, index) or has_loose_bvar(body, index + 1)
        case Let(_, binder_type, value, body, _):
            return (
                has_loose_bvar(binder_type, index)
                or has_loose_bvar(value, index)
                or has_loose_bvar(body, index + 1)
            )
        case Projection(_, _, struct):
            return has_loose_bvar(struct, index)
        case MData(inner, _):
            return has_loose_bvar(inner, index)
        case _:
            return False


def mk_name(*parts: str) -> Name:
    """
    The hierarchical name `parts[0].parts[1]...`, e.g. `mk_name("Nat", "succ")` is `Nat.succ`.
    """
    name: Name = Anon()
    for part in parts:
        name = StrName(name, part)
    return name


def ensure_parameters_unique(parameters: tuple[Name, ...]) -> None:
    seen_names = set()
    for name in parameters:
        if name in seen_names:
            raise KernelError(f"duplicate level parameter: {name}")
        seen_names.add(name)


def mentions_constant(expr: Expr, names: Collection[Name]) -> bool:
    """
    True iff a constant named in `names` occurs in `expr`.
    """
    match expr:
        case Const(name, _):
            return name in names
        case App(fn, arg):
            return mentions_constant(fn, names) or mentions_constant(arg, names)
        case Lambda(_, binder_type, _, body) | Forall(_, binder_type, _, body):
            return mentions_constant(binder_type, names) or mentions_constant(body, names)
        case Let(_, binder_type, value, body, _):
            return any(mentions_constant(e, names) for e in (binder_type, value, body))
        case Projection(_, _, struct):
            return mentions_constant(struct, names)
        case MData(inner, _):
            return mentions_constant(inner, names)
        case _:
            return False


def erase_binder_names(expr: Expr) -> Expr:
    """
    `expr` with all binder names and binder infos replaced by defaults, and metadata removed:
    none of these matter for type checking.
    """
    match expr:
        case App(fn, arg):
            return App(erase_binder_names(fn), erase_binder_names(arg))
        case Lambda(_, binder_type, _, body):
            return Lambda(Anon(), erase_binder_names(binder_type), "default", erase_binder_names(body))
        case Forall(_, binder_type, _, body):
            return Forall(Anon(), erase_binder_names(binder_type), "default", erase_binder_names(body))
        case Let(_, binder_type, value, body, nondep):
            return Let(
                Anon(),
                erase_binder_names(binder_type),
                erase_binder_names(value),
                erase_binder_names(body),
                nondep,
            )
        case Projection(type_name, index, struct):
            return Projection(type_name, index, erase_binder_names(struct))
        case MData(inner, _):
            return erase_binder_names(inner)
        case _:
            return expr


def consume_type_annotations(type_: Expr) -> Expr:
    """
    `type_` without the annotations the elaborator puts on binder types, e.g. `outParam α` is
    `α`. These are definitions that just return their type argument, and the official kernel
    removes them from the binder types of the generated recursors.
    """
    match type_:
        case App(Const(name, _), inner) if name in (
            mk_name("outParam"),
            mk_name("semiOutParam"),
        ):
            return consume_type_annotations(inner)
        case App(App(Const(name, _), inner), _) if name in (
            mk_name("optParam"),
            mk_name("autoParam"),
        ):
            return consume_type_annotations(inner)
        case _:
            return type_
