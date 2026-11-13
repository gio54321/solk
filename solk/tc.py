from ast import Not

from loguru import logger

from solk.parser import ExportedDefinitions
from solk.types import (
    App,
    Axiom,
    BinderInfo,
    BVar,
    Const,
    Constructor,
    Declaration,
    DeclarationInfo,
    Definition,
    Expr,
    Forall,
    FVar,
    IMax,
    Inductive,
    InductiveBlock,
    Lambda,
    Let,
    Level,
    Max,
    MData,
    Name,
    NatLiteral,
    Opaque,
    Param,
    Projection,
    Quot,
    Recursor,
    Sort,
    StringLiteral,
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
            case Definition():
                check_definition(self, decl)
            case Theorem():
                check_theorem(self, decl)
            case Opaque():
                check_opaque(self, decl)
            case _:
                # TODO: Quot and InductiveBlock
                return
        self.constants[decl.info.name] = decl


def check_axiom(env: Environment, axiom: Axiom) -> None:
    if axiom.is_unsafe:
        raise KernelError(f"unsafe axiom: {axiom}")
    check_declaration_info(env, axiom.info)


def check_definition(env: Environment, definition: Definition) -> None:
    # unsafe definitions can be recursive and partial ones are only allowed to be referenced by
    # other partial or unsafe declarations: we only accept safe ones
    if definition.safety != "safe":
        raise KernelError(f"{definition.safety} definition: {definition}")
    check_declaration_info(env, definition.info)
    check_value(env, definition.info, definition.value)


def check_theorem(env: Environment, theorem: Theorem) -> None:
    # a theorem is a definition whose type is a proposition, i.e. whose type has type Prop
    sort = check_declaration_info(env, theorem.info)
    if not normalizes_to_zero_level(sort.level):
        raise KernelError(f"theorem type is not a proposition: {theorem.info.declaration_type}")
    check_value(env, theorem.info, theorem.value)


def check_opaque(env: Environment, opaque: Opaque) -> None:
    # an opaque is checked exactly like a definition: the only difference is that its value is
    # never unfolded afterwards (see `whnf`)
    if opaque.is_unsafe:
        raise KernelError(f"unsafe opaque: {opaque}")
    check_declaration_info(env, opaque.info)
    check_value(env, opaque.info, opaque.value)


def check_value(env: Environment, info: DeclarationInfo, value: Expr) -> None:
    """
    Check that `value` is a closed term of type `info.declaration_type`.
    """
    if has_free_variables(value):
        raise KernelError(f"declaration value has free variables: {value}")

    tc = TypeChecker(env, info)
    value_type = tc.infer_term(value)
    if not tc.def_eq(value_type, info.declaration_type):
        raise KernelError(
            f"value has type {value_type}, but is declared with type {info.declaration_type}"
        )


def check_declaration_info(env: Environment, info: DeclarationInfo) -> Sort:
    """
    Check the header of a declaration: its name, universe parameters and type.
    Return the sort of the type, i.e. the `Sort u` such that `info.declaration_type : Sort u`.
    """
    # ensure that the name is not already taken
    if info.name in env.constants:
        raise KernelError(f"already declared: {info.name}")

    # ensure that the universe parameters are unique
    ensure_parameters_unique(info.level_params)

    # ensure that the type does not have free variables
    if has_free_variables(info.declaration_type):
        raise KernelError(
            f"declaration type has free variables: {info.declaration_type}"
        )

    # ensure that the type of the declaration type is a Sort _
    tc = TypeChecker(env, info)
    inferred_type = tc.whnf(tc.infer_term(info.declaration_type))
    if not isinstance(inferred_type, Sort):
        raise KernelError(f"declaration type is not a sort: {inferred_type}")
    return inferred_type


class TypeChecker:
    def __init__(
        self, env: Environment, declaring_info: DeclarationInfo | None = None
    ) -> None:
        self.env = env
        self.declaring_info = declaring_info
        self.free_variables: dict[str, Expr] = {}

    def new_free_variable(self, fvar_type: Expr) -> FVar:
        name = f"fvar_{len(self.free_variables)}"
        fvar = FVar(name=name)
        self.free_variables[name] = fvar_type
        return fvar

    def infer_term(self, term: Expr) -> Expr:
        match term:
            case BVar(_index):
                raise KernelError(f"bound variable not allowed in inference: {_index}")
            case FVar(name):
                if name not in self.free_variables:
                    raise KernelError(f"free variable not found: {name}")
                return self.free_variables[name]
            case Const():
                return self.infer_const(term)
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
            case Projection():
                return self.infer_projection(term)
            case NatLiteral() | StringLiteral():
                raise NotImplementedError
            case _:
                raise NotImplementedError

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
        fun_type = self.whnf(self.infer_term(app.fn))
        if not isinstance(fun_type, Forall):
            raise KernelError(f"expected a forall type, got {fun_type}")

        # get the type of the argument
        arg_type = self.infer_term(app.arg)

        # the binder type must match the argument type
        if not self.def_eq(fun_type.binder_type, arg_type):
            raise KernelError(f"expected {fun_type.binder_type}, got {arg_type}")

        # the type of the application is the return value of the pi,
        # instantiated with the argument value
        return instantiate(fun_type.body, app.arg)

    def infer_lambda(self, lam: Lambda) -> Expr:
        # the type of the binder type must be a sort
        binder_type_type = self.whnf(self.infer_term(lam.binder_type))
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
        binder_type_type = self.whnf(self.infer_term(pi.binder_type))
        if not isinstance(binder_type_type, Sort):
            raise KernelError(f"expected a sort, got {binder_type_type}")

        # replce the binder with a fresh free variable and infer the body type
        fvar = self.new_free_variable(pi.binder_type)
        body = instantiate(pi.body, fvar)
        body_type = self.whnf(self.infer_term(body))

        # we are in a pi, so the body type must also be a sort
        if not isinstance(body_type, Sort):
            raise KernelError(f"expected a sort, got {body_type}")

        # the type of a pi is the sort IMax(binder sort level, body sort level)
        return Sort(IMax(binder_type_type.level, body_type.level))

    def infer_let(self, let: Let) -> Expr:
        # the type of the binder type must be a sort
        binder_type_type = self.whnf(self.infer_term(let.binder_type))
        if not isinstance(binder_type_type, Sort):
            raise KernelError(f"expected a sort, got {binder_type_type}")

        # the type of the value must be equal to the binder type
        value_type = self.infer_term(let.value)
        if not self.def_eq(let.binder_type, value_type):
            raise KernelError(
                f"binder type {let.binder_type} does not match value type {value_type}"
            )

        # the type of a let x: A = val in body is
        # the type of the body with x replaced by val
        body = instantiate(let.body, let.value)
        return self.infer_term(body)

    def infer_const(self, const: Const) -> Expr:
        # find the term in the environment
        if const.name not in self.env.constants:
            raise KernelError(f"undeclared constant: {const.name}")
        term = self.env.get(const.name)

        # instantiate all universe parameters with the concrete universes in const.universes
        if self.declaring_info is not None:
            # check that all universe parameters referenced in the universe parameters we need to
            # substitute in the term are bound by the current declaration
            for uparam in const.universes:
                if not all_uparams_defined(uparam, self.declaring_info.level_params):
                    raise KernelError(f"universe parameter {uparam} not defined")

        declaration_type = get_declaration_info(term).declaration_type

        # by induction on the env, this term has already been type checked to be of type `declaration_type`
        # the only thing left to do is to instantiate the universe parameters of the declaration using
        # the concrete universe levels provided in the const term
        universe_parameters = get_universe_parameters(term)
        if len(universe_parameters) != len(const.universes):
            raise KernelError(f"universe parameter count mismatch for {const.name}")

        return instantiate_universe_parameters(
            declaration_type, universe_parameters, const.universes
        )

    def infer_projection(self, proj: Projection) -> Expr:
        raise NotImplementedError

    def def_eq(self, t: Expr, s: Expr) -> bool:

        # check definitional equality by proof irrelevance
        type_t = self.infer_term(t)
        type_s = self.infer_term(s)

        # if the type of t is a Prop (i.e., t is a proof term), then
        # by proof irrelevance, any proof for the same proposition is definitionally
        # equal. Therefore, it suffices to check definitional equality of the types
        # of t and s
        type_type_t = self.whnf(self.infer_term(type_t))
        if isinstance(type_type_t, Sort):
            if normalizes_to_zero_level(type_type_t.level):
                return self.def_eq(type_t, type_s)


        # TODO: I wish it was this easy...
        return t == s

    def whnf(self, expr: Expr) -> Expr:
        match expr:
            case MData(inner, _):
                # metadata is irrelevant for the kernel
                return self.whnf(inner)

            case Let(_, _, value, body, _):
                # zeta rule:
                # let x := value; body -> body[x := value]
                return self.whnf(instantiate(body, value))

            case App(fn, arg):
                # first bring the function to whnf: for `f a b`, this means reducing `f a`
                fn = self.whnf(fn)
                if isinstance(fn, Lambda):
                    # beta rule:
                    # (lambda x, body) arg -> body[x := arg]
                    return self.whnf(instantiate(fn.body, arg))
                # TODO: iota, i.e. `fn arg` is a fully applied recursor whose major premise reduces
                # to a constructor
                return App(fn, arg)

            case Const(name, universes):
                # delta rule: the value of a constant is the value of its definition.
                # only definitions and theorems have a value. Axioms, opaque definitions,
                # inductive types, constructors and recursors are stuck.
                decl = self.env.constants.get(name)
                if not isinstance(decl, (Definition, Theorem)):
                    return expr
                if len(universes) != len(decl.info.level_params):
                    return expr
                value = instantiate_universe_parameters(
                    decl.value, decl.info.level_params, universes
                )
                return self.whnf(value)

            case Projection(type_name, index, struct):
                # proj: the structure must reduce to a constructor application `S.mk args`
                struct = self.whnf(struct)
                # TODO: string literals are structures (`String.ofList [chars]`) and can be projected
                if isinstance(struct, StringLiteral):
                    raise NotImplementedError("projection out of a string literal")

                # split `S.mk a0 ... ak` into the head `S.mk` and the arguments `[a0, ..., ak]`
                ctor: Expr = struct
                args: list[Expr] = []
                while isinstance(ctor, App):
                    args.insert(0, ctor.arg)
                    ctor = ctor.fn

                if not isinstance(ctor, Const):
                    return expr
                decl = self.env.constants.get(ctor.name)
                if not isinstance(decl, Constructor) or decl.inductive_name != type_name:
                    return expr

                # the arguments of the constructor are the parameters of `S`, then its fields
                field = decl.num_params + index
                if field >= len(args):
                    return expr  # partially applied constructor
                return self.whnf(args[field])

            case _:
                # everything else is already in whnf
                return expr

def normalizes_to_zero_level(level: Level) -> bool:
    match level:
        case Zero():
            return True
        case Succ():
            return False
        case Param():
            return False
        case Max(left, right):
            return normalizes_to_zero_level(left) and normalizes_to_zero_level(right)
        case IMax(left, right):
            return normalizes_to_zero_level(right)        


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
                    instantiate_level_universe_parameters(
                        universe, parameters, universes
                    )
                )
            return Const(name, tuple(output_universes))
        case Sort(level=level):
            return Sort(
                instantiate_level_universe_parameters(level, parameters, universes)
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


def instantiate_level_universe_parameters(
    level: Level, parameters: tuple[Name, ...], universes: tuple[Level, ...]
) -> Level:
    match level:
        case Zero():
            return Zero()
        case Succ(pred=pred):
            return Succ(
                instantiate_level_universe_parameters(pred, parameters, universes)
            )
        case Param(name=name):
            for param, universe in zip(parameters, universes):
                if name == param:
                    return universe
            return Param(name)
        case Max(left=left, right=right):
            return Max(
                instantiate_level_universe_parameters(left, parameters, universes),
                instantiate_level_universe_parameters(right, parameters, universes),
            )
        case IMax(left=left, right=right):
            return IMax(
                instantiate_level_universe_parameters(left, parameters, universes),
                instantiate_level_universe_parameters(right, parameters, universes),
            )


def get_universe_parameters(declaration: ConstantInfo) -> tuple[Name, ...]:
    return get_declaration_info(declaration).level_params


def get_declaration_info(declaration: ConstantInfo) -> DeclarationInfo:
    match declaration:
        case Definition(declaration_info):
            return declaration_info
        case Axiom(declaration_info):
            return declaration_info
        case Theorem(declaration_info):
            return declaration_info
        case Opaque(declaration_info):
            return declaration_info
        case Quot(declaration_info):
            return declaration_info
        case Inductive(declaration_info):
            return declaration_info
        case _:
            raise KernelError(
                f"trying to retrieve declaration info for declaration {declaration}"
            )


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
