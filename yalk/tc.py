from loguru import logger

from yalk.parser import ExportedDefinitions
from yalk.types import (
    App,
    Axiom,
    BVar,
    Constructor,
    Declaration,
    DeclarationInfo,
    Definition,
    Expr,
    Forall,
    FVar,
    IMax,
    Inductive,
    Lambda,
    Let,
    Level,
    Max,
    Name,
    Opaque,
    Param,
    Projection,
    Quot,
    Recursor,
    Sort,
    Succ,
    Theorem,
    Zero,
)

ConstantInfo = (
    Axiom | Definition | Theorem | Opaque | Quot | Inductive | Constructor | Recursor
)


class KernelError(Exception):
    pass


class Environment:
    def __init__(self) -> None:
        self.constants: dict[Name, ConstantInfo] = {}

    def get(self, name: Name) -> ConstantInfo:
        if name not in self.constants:
            raise KernelError(f"undeclared constant: {name}")
        return self.constants[name]

    def add_all(self, exported: ExportedDefinitions) -> None:
        for decl in exported.declarations:
            self.add(decl)

    def add(self, decl: Declaration) -> None:
        match decl:
            case Axiom():
                check_axiom(self, decl)
                self.constants[decl.info.name] = decl
            case _:
                pass
                # raise NotImplementedError(f"checking {type(decl)} not implemented")


def check_axiom(env: Environment, axiom: Axiom) -> None:
    if axiom.is_unsafe:
        raise KernelError(f"unsafe axiom: {axiom}")
    check_declaration_info(env, axiom.info)


def check_declaration_info(env: Environment, info: DeclarationInfo) -> None:
    # ensure that the universe parameters are unique
    ensure_parameters_unique(info.level_params)

    # ensure that the type does not have free variables
    if has_free_variables(info.declaration_type):
        raise KernelError(
            f"declaration type has free variables: {info.declaration_type}"
        )

    # ensure that the type of the declaration type is a Sort _
    tc = TypeChecker(env, info)
    inferred_type = tc.infer_term(info.declaration_type)


class TypeChecker:
    def __init__(
        self, env: Environment, declaring_info: DeclarationInfo | None = None
    ) -> None:
        self.env = env
        self.locals: list[Expr] = []
        self.declaring_info: DeclarationInfo | None = None

    def infer_term(self, term: Expr) -> Expr:
        match term:
            case BVar(_index):
                pass  # TODO
            case FVar(name):
                raise KernelError(f"free variable not allowed in inference: {name}")
            case Sort():
                return self.infer_sort(term)
            case App():
                return self.infer_app(term)
        return Sort(Zero())

    def infer_sort(self, sort: Sort) -> Expr:
        if self.declaring_info is not None and not all_uparams_defined(
            sort.level, self.declaring_info.level_params
        ):
            raise KernelError(
                f"level {sort.level} contains undefined universe parameters"
            )

        # The type of Sort n is Sort (succ n)
        return Sort(Succ(sort.level))

    def infer_app(self, app: App) -> Expr:
        fun_type = whnf(self.infer_term(app.fn))
        if not isinstance(fun_type, Forall):
            raise KernelError(f"expected a forall type, got {fun_type}")

        arg_type = self.infer_term(app.arg)

        # get the concrete type of the binder, which could be dependent on the argument value
        concrete_binder_type = instantiate(fun_type.binder_type, app.arg)

        if not def_eq(concrete_binder_type, arg_type):
            raise KernelError(f"expected {concrete_binder_type}, got {arg_type}")

        return instantiate(fun_type.body, app.arg)


def def_eq(expr1: Expr, expr2: Expr) -> bool:
    # TODO: I wish it was this easy...
    return expr1 == expr2

def whnf(expr: Expr) -> Expr:
    # TODO
    return expr

def instantiate(expr: Expr, arg: Expr, offset: int = 0) -> Expr:
    match expr:
        case BVar(index):
            return arg if index == offset else expr
        case App(fn, arg):
            return App(instantiate(fn, arg, offset), instantiate(arg, arg, offset))
        case Lambda(var, binder_type, binder_info, body):
            return Lambda(var, instantiate(binder_type, arg, offset), binder_info, instantiate(body, arg, offset + 1))
        case Forall(var, binder_type, binder_info, body):
            return Forall(var, instantiate(binder_type, arg, offset), binder_info, instantiate(body, arg, offset + 1))
        case Let(var, binder_type, value, body, nondep):
            return Let(var, instantiate(binder_type, arg, offset), instantiate(value, arg, offset), instantiate(body, arg, offset + 1), nondep)
        case Projection(type_name=type_name, index=index, struct=struct):
            return Projection(type_name, index, instantiate(struct, arg, offset))
        case _:
            return expr


def num_loose_bound_variables(expr: Expr) -> int:
    # compute the number of loose bound variables in the expression. This is the number of
    # variables that are not bound internally by the expression itself.
    match expr:
        case BVar(index):
            return index + 1
        case App(fn, arg):
            return max(
                num_loose_bound_variables(fn),
                max(num_loose_bound_variables(arg) - 1, 0),
            )
        case Lambda(binder_type=binder_type, body=body):
            return max(
                num_loose_bound_variables(binder_type),
                max(num_loose_bound_variables(body) - 1, 0),
            )
        case Forall(binder_type=binder_type, body=body):
            return max(
                num_loose_bound_variables(binder_type),
                max(num_loose_bound_variables(body) - 1, 0),
            )
        case Let(binder_type=binder_type, value=value, body=body):
            return max(
                num_loose_bound_variables(binder_type),
                num_loose_bound_variables(value),
                max(num_loose_bound_variables(body) - 1, 0),
            )
        case Projection(struct=struct):
            return num_loose_bound_variables(struct)
        case _:
            return 0


def ensure_parameters_unique(parameters: tuple[Name, ...]) -> None:
    seen_names = set()
    for name in parameters:
        if name in seen_names:
            raise KernelError(f"duplicate level parameter: {name}")
        seen_names.add(name)


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


def all_uparams_defined(level: Level, parameters: tuple[Name, ...]) -> bool:
    # return true if all universe parameters referenced in level are in parameters
    match level:
        case Zero():
            return True
        case Succ(pred):
            return all_uparams_defined(pred, parameters)
        case Max(left, right):
            return all_uparams_defined(left, parameters) and all_uparams_defined(
                right, parameters
            )
        case IMax(left, right):
            return all_uparams_defined(left, parameters) and all_uparams_defined(
                right, parameters
            )
        case Param(name):
            return name in parameters
