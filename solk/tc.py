from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING

from solk.levels import all_uparams_defined, is_zero
from solk.types import (
    Anon,
    App,
    BVar,
    Const,
    Constructor,
    DeclarationInfo,
    Definition,
    Expr,
    Forall,
    FVar,
    IMax,
    Lambda,
    Let,
    MData,
    NatLiteral,
    Projection,
    Sort,
    StringLiteral,
    Succ,
    Theorem,
)
from solk.utils import (
    KernelError,
    abstract,
    instantiate,
    instantiate_universe_parameters,
)

if TYPE_CHECKING:
    from solk.environment import Environment


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

    def type_of(self, fvar: FVar) -> Expr:
        return self.free_variables[fvar.name]

    def pi(self, fvars: Sequence[FVar], body: Expr) -> Expr:
        """
        `(x1 : T1) → ... → (xn : Tn) → body`, binding the free variables `fvars = [x1, ..., xn]`.
        """
        for fvar in reversed(fvars):
            body = Forall(Anon(), self.type_of(fvar), "default", abstract(body, fvar))
        return body

    def lam(self, fvars: Sequence[FVar], body: Expr) -> Expr:
        """
        `fun (x1 : T1) ... (xn : Tn) => body`, binding the free variables `fvars = [x1, ..., xn]`.
        """
        for fvar in reversed(fvars):
            body = Lambda(Anon(), self.type_of(fvar), "default", abstract(body, fvar))
        return body

    def is_proof(self, term: Expr) -> bool:
        """
        True iff `term` is a proof, i.e. its type is a proposition, i.e. its type has type `Prop`.
        """
        sort = self.whnf(self.infer_term(self.infer_term(term)))
        return isinstance(sort, Sort) and is_zero(sort.level)

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

        # by induction on the env, this term has already been type checked to be of type `declaration_type`
        # the only thing left to do is to instantiate the universe parameters of the declaration using
        # the concrete universe levels provided in the const term
        if len(term.info.level_params) != len(const.universes):
            raise KernelError(f"universe parameter count mismatch for {const.name}")

        return instantiate_universe_parameters(
            term.info.declaration_type, term.info.level_params, const.universes
        )

    def infer_projection(self, proj: Projection) -> Expr:
        raise NotImplementedError

    def def_eq(self, t: Expr, s: Expr) -> bool:
        # if t is a proof, then by proof irrelevance, any proof of the same proposition is
        # definitionally equal to it. Therefore, it suffices to check definitional equality of
        # the types of t and s
        if self.is_proof(t):
            return self.def_eq(self.infer_term(t), self.infer_term(s))

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
