import re

from loguru import logger

from yalk.parser import ExportedDefinitions
from yalk.types import (
    App,
    Axiom,
    BVar,
    BinderInfo,
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
        self.declaring_info: DeclarationInfo | None = None
        self.free_variables: dict[FVar, Expr] = {}

    def new_free_variable(self, fvar_type: Expr) -> FVar:
        fvar = FVar(name=f"fvar_{len(self.free_variables)}")
        self.free_variables[fvar] = fvar_type
        return fvar

    def infer_term(self, term: Expr) -> Expr:
        match term:
            case BVar(_index):
                raise KernelError(f"bound variable not allowed in inference: {_index}")
            case FVar(name):
                if name not in self.free_variables:
                    raise KernelError(f"free variable not found: {name}")
                return self.free_variables[name]
            case Sort():
                return self.infer_sort(term)
            case App():
                return self.infer_app(term)
            case Lambda():
                return self.infer_lambda(term)
            case Forall():
                return self.infer_pi(term)
            case Let():
                return self.infer_let(term)
        return Sort(Zero())

    def infer_sort(self, sort: Sort) -> Expr:
        # all the universe parameters referenced in the sort must be defined
        if self.declaring_info is not None and not all_uparams_defined(
            sort.level, self.declaring_info.level_params
        ):
            raise KernelError(
                f"level {sort.level} contains undefined universe parameters"
            )

        # the type of Sort n is Sort (succ n)
        return Sort(Succ(sort.level))

    def infer_app(self, app: App) -> Expr:
        # get the type of the function, it must be pi
        fun_type = whnf(self.infer_term(app.fn))
        if not isinstance(fun_type, Forall):
            raise KernelError(f"expected a forall type, got {fun_type}")

        # get the type of the argument
        arg_type = self.infer_term(app.arg)

        # the binder type must match the argument type
        if not def_eq(fun_type.binder_type, arg_type):
            raise KernelError(f"expected {fun_type.binder_type}, got {arg_type}")

        # the type of the application is the return value of the pi,
        # instantiated with the argument value
        return instantiate(fun_type.body, app.arg)

    def infer_lambda(self, lam: Lambda) -> Expr:
        # the type of the binder type must be a sort
        binder_type_type = whnf(self.infer_term(lam.binder_type))
        if not isinstance(binder_type_type, Sort):
            raise KernelError(f"expected a sort, got {binder_type_type}")

        # replce the binder with a fresh free variable and infer the body type
        fvar = self.new_free_variable(lam.binder_type)
        body = instantiate(lam.body, fvar)
        body_type = self.infer_term(body)

        # at this point, the body type is inferred, but it could contain occurrences of the
        # newly created free variable, because the body type could be dependent on the binder value.
        # to construct a pi, we need to bind those occurrences, so we conert them back to the corresponding
        # bound variables, referencing the binder immediately above
        body_type_abstracted = abstract(body_type, fvar)

        # the type of the lambda is a pi, with the binder type as the domain and the body as the codomain
        return Forall(lam.var, lam.binder_type, lam.binder_info, body_type_abstracted)

    def infer_pi(self, pi: Forall) -> Expr:
        # the type of the binder type must be a sort
        binder_type_type = whnf(self.infer_term(pi.binder_type))
        if not isinstance(binder_type_type, Sort):
            raise KernelError(f"expected a sort, got {binder_type_type}")

        # replce the binder with a fresh free variable and infer the body type
        fvar = self.new_free_variable(pi.binder_type)
        body = instantiate(pi.body, fvar)
        body_type = whnf(self.infer_term(body))

        # we are in a pi, so the body type must also be a sort
        if not isinstance(body_type, Sort):
            raise KernelError(f"expected a sort, got {body_type}")

        # the type of a pi is the sort IMax(binder sort level, body sort level)
        return Sort(IMax(binder_type_type.level, body_type.level))

    def infer_let(self, let: Let) -> Expr:
        # the type of the binder type must be a sort
        binder_type_type = whnf(self.infer_term(let.binder_type))
        if not isinstance(binder_type_type, Sort):
            raise KernelError(f"expected a sort, got {binder_type_type}")

        # the type of the value must be equal to the binder type
        value_type = self.infer_term(let.value)
        if not def_eq(let.binder_type, value_type):
            raise KernelError(f"binder type {let.binder_type} does not match value type {value_type}")

        # the type of a let x: A = val in body is
        # the type of the body with x replaced by val
        body = instantiate(let.body, let.value)
        return self.infer_term(body)

def def_eq(expr1: Expr, expr2: Expr) -> bool:
    # TODO: I wish it was this easy...
    return expr1 == expr2

def whnf(expr: Expr) -> Expr:
    # TODO
    return expr

def instantiate(expr: Expr, arg: Expr, offset: int = 0) -> Expr:
    """
    Instantiate the bound variable at the current offset with the given argument `arg`.
    By default offset is 0, so the bound variable immediately "above" is instantiated.
    """
    match expr:
        case BVar(index):
            return arg if index == offset else expr
        case App(fn, arg_inner):
            return App(instantiate(fn, arg, offset), instantiate(arg_inner, arg, offset))
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

def abstract(expr: Expr, fvar: FVar, offset: int = 0) -> Expr:
    """
    Abstract the free variable `fvar` from the expression `expr` with the correct De Bruijn index.
    """
    match expr:
        case FVar(index):
            return BVar(offset) if index == offset else expr
        case App(fn, arg_inner):
            return App(abstract(fn, fvar, offset), abstract(arg_inner, fvar, offset))
        case Lambda(var, binder_type, binder_info, body):
            return Lambda(var, abstract(binder_type, fvar, offset), binder_info, abstract(body, fvar, offset + 1))
        case Forall(var, binder_type, binder_info, body):
            return Forall(var, abstract(binder_type, fvar, offset), binder_info, abstract(body, fvar, offset + 1))
        case Let(var, binder_type, value, body, nondep):
            return Let(var, abstract(binder_type, fvar, offset), abstract(value, fvar, offset), abstract(body, fvar, offset + 1), nondep)
        case Projection(type_name=type_name, index=index, struct=struct):
            return Projection(type_name, index, abstract(struct, fvar, offset))
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
