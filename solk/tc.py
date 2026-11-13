from __future__ import annotations

import math
from collections.abc import Sequence
from typing import TYPE_CHECKING

from solk.levels import all_uparams_defined, is_zero, level_equiv
from solk.literals import (
    BOOL_FALSE,
    BOOL_TRUE,
    NAT,
    NAT_BINARY_OPS,
    NAT_SUCC,
    STRING,
    literal_to_constructor,
    nat_lit_to_constructor,
    nat_predecessor,
    nat_value,
    string_lit_to_constructor,
)
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
    Inductive,
    Lambda,
    Let,
    MData,
    Name,
    NatLiteral,
    Projection,
    Quot,
    Recursor,
    RegularHint,
    Sort,
    StringLiteral,
    StrName,
    Succ,
    Theorem,
)
from solk.utils import (
    KernelError,
    abstract,
    get_fn,
    get_head,
    get_num_args,
    has_free_variables,
    has_loose_bvar,
    instantiate,
    instantiate_universe_parameters,
    replace_fn,
)

if TYPE_CHECKING:
    from solk.environment import Environment


def unfold_order(decl: Definition | Theorem) -> float:
    """
    In lazy delta reduction, the definition with the greatest order is unfolded first. A
    definition's height is greater than the heights of the definitions in its value, so unfolding
    the highest first may reveal the other one. Abbreviations are unfolded first, theorems and
    definitions marked opaque last.
    """
    match decl:
        case Definition(hints=RegularHint(height)):
            return height
        case Definition(hints="abbrev"):
            return math.inf
        case _:
            return -1


def major_inductive(rec: Recursor) -> Name:
    """
    The inductive type `I` of the major premise of the recursor `I.rec`.
    """
    assert isinstance(rec.info.name, StrName)
    return rec.info.name.pre


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

    def is_prop(self, type_: Expr) -> bool:
        """
        True iff `type_` is a proposition, i.e. it has type `Prop`.
        """
        sort = self.whnf(self.infer_term(type_))
        return isinstance(sort, Sort) and is_zero(sort.level)

    def is_proof(self, term: Expr) -> bool:
        """
        True iff `term` is a proof, i.e. its type is a proposition.
        """
        return self.is_prop(self.infer_term(term))

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
            case NatLiteral():
                return NAT
            case StringLiteral():
                return STRING
            case MData(inner, _):
                return self.infer_term(inner)

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
        """
        If `struct : S params`, the type of `struct.i` is the type of the `i`-th field of
        `S.mk params : (fields) → S params`, where the previous fields are replaced by their
        projections out of `struct`.
        """
        struct_type = self.whnf(self.infer_term(proj.struct))
        struct = get_head(struct_type)
        decl = self.env.constants.get(proj.type_name)
        if (
            not isinstance(struct, Const)
            or struct.name != proj.type_name
            or not isinstance(decl, Inductive)
            or len(decl.constructor_names) != 1
            or get_num_args(struct_type) != decl.num_params + decl.num_indices
        ):
            raise KernelError(f"invalid projection: {proj}")

        # the type of `S.mk params`: replace `S` with `S.mk` in `S params indices`, without indices
        ctor = Const(decl.constructor_names[0], struct.universes)
        ctor_app = replace_fn(get_fn(struct_type, decl.num_indices), decl.num_params, ctor)
        type_ = self.infer_term(ctor_app)

        # a proof contains no data: only proofs can be projected out of a proof, and the type
        # of a field cannot depend on a data field (it would expose that data)
        is_prop = self.is_prop(struct_type)
        for i in range(proj.index):
            type_ = self.whnf(type_)
            if not isinstance(type_, Forall):
                raise KernelError(f"invalid projection: {proj}")
            if is_prop and has_loose_bvar(type_.body) and not self.is_prop(type_.binder_type):
                raise KernelError(f"projection depends on data of a proof: {proj}")
            type_ = instantiate(type_.body, Projection(proj.type_name, i, proj.struct))

        type_ = self.whnf(type_)
        if not isinstance(type_, Forall):
            raise KernelError(f"invalid projection: {proj}")
        if is_prop and not self.is_prop(type_.binder_type):
            raise KernelError(f"projection of data out of a proof: {proj}")
        return type_.binder_type

    def def_eq(self, t: Expr, s: Expr) -> bool:
        """
        True if `t` and `s` are definitionally equal. Full definitional equality is undecidable:
        like the official kernel, this check is sound, but it may reject equal terms or not
        terminate.

        Same steps as `is_def_eq_core` in the official kernel.
        """
        quick = self.def_eq_quick(t, s)
        if quick is not None:
            return quick

        # proofs by reflection, such as those of the `decide` tactic, compare a closed boolean
        # computation with `true`: evaluating it is much faster than comparing step by step
        if s == BOOL_TRUE and not has_free_variables(t) and self.whnf(t) == BOOL_TRUE:
            return True

        # if t is a proof, then by proof irrelevance, any proof of the same proposition is
        # definitionally equal to it. Therefore, it suffices to check definitional equality of
        # the types of t and s
        if self.is_proof(t):
            return self.def_eq(self.infer_term(t), self.infer_term(s))

        return self.def_eq_lazy(t, s)

    def def_eq_quick(self, t: Expr, s: Expr) -> bool | None:
        """
        The cheap cases, which need no reduction. None if they do not apply.
        """
        if t == s:
            return True
        if isinstance(t, Sort) and isinstance(s, Sort):
            return level_equiv(t.level, s.level)
        if (isinstance(t, Lambda) and isinstance(s, Lambda)) or (
            isinstance(t, Forall) and isinstance(s, Forall)
        ):
            return self.def_eq_binder(t, s)
        return None

    def def_eq_lazy(self, t: Expr, s: Expr) -> bool:
        """
        `t =?= s`, for `t` and `s` which are not proofs: reduce them, unfolding definitions
        lazily, and compare them. Reduction does not change the type, so the reduced terms
        are not proofs either.
        """
        # reduce, except for unfolding definitions, and retry the cheap cases
        t, s = self.whnf_core(t), self.whnf_core(s)
        quick = self.def_eq_quick(t, s)
        if quick is not None:
            return quick

        # `n + 1 =?= m + 1` iff `n =?= m`, where `n + 1` is either `Nat.succ n` or a literal
        t_pred, s_pred = nat_predecessor(t), nat_predecessor(s)
        if t_pred is not None and s_pred is not None:
            return self.def_eq(t_pred, s_pred)

        # compute arithmetic on literals, e.g. `Nat.add 2 2 =?= 4`. With free variables, the
        # arguments are unlikely to reduce to literals, so we do not even try
        if not has_free_variables(t) and not has_free_variables(s):
            t_value = self.reduce_nat(t)
            if t_value is not None:
                return self.def_eq(t_value, s)
            s_value = self.reduce_nat(s)
            if s_value is not None:
                return self.def_eq(t, s_value)

        # lazy delta reduction: unfold definitions one at a time, hoping to find equal terms
        # without unfolding everything. E.g. `f (1 + 1) =?= f 2` holds without unfolding `f`,
        # which may be very expensive to compute
        t_decl, s_decl = self.unfoldable(t), self.unfoldable(s)
        if t_decl is not None or s_decl is not None:
            # same definition on both sides: first try to compare the arguments
            if (
                t_decl is s_decl
                and isinstance(t_decl, Definition)
                and isinstance(t_decl.hints, RegularHint)
                and self.def_eq_args(t, s)
            ):
                return True

            # otherwise, unfold the definition that comes first in `unfold_order`, or both
            t_order = None if t_decl is None else unfold_order(t_decl)
            s_order = None if s_decl is None else unfold_order(s_decl)
            if t_order is not None and (s_order is None or t_order >= s_order):
                t = self.unfold_definition(t) or t
            if s_order is not None and (t_order is None or s_order >= t_order):
                s = self.unfold_definition(s) or s
            return self.def_eq_lazy(t, s)

        # both terms are in whnf: compare them piece by piece
        if self.def_eq_stuck(t, s):
            return True

        # a literal is equal to its constructor form, e.g. `3 =?= Nat.succ n` iff
        # `Nat.succ 2 =?= Nat.succ n`. Two different literals are never equal.
        literal = NatLiteral | StringLiteral
        if isinstance(t, literal) and not isinstance(s, literal):
            return self.def_eq(literal_to_constructor(t), s)
        if isinstance(s, literal) and not isinstance(t, literal):
            return self.def_eq(t, literal_to_constructor(s))

        # the eta rules, which reduction alone cannot see
        return (
            self.def_eq_eta(t, s)
            or self.def_eq_eta(s, t)
            or self.def_eq_eta_struct(t, s)
            or self.def_eq_eta_struct(s, t)
            or self.def_eq_unit_like(t, s)
        )

    def def_eq_binder(self, t: Lambda | Forall, s: Lambda | Forall) -> bool:
        """
        `fun (x : A) => b` and `fun (y : A') => b'` are definitionally equal iff `A` and `A'` are,
        and so are `b` and `b'` with `x` and `y` replaced by the same fresh free variable.
        Same for pi types. Binder names and infos are irrelevant.
        """
        if not self.def_eq(t.binder_type, s.binder_type):
            return False
        fvar = self.new_free_variable(t.binder_type)
        return self.def_eq(instantiate(t.body, fvar), instantiate(s.body, fvar))

    def def_eq_stuck(self, t: Expr, s: Expr) -> bool:
        """
        Congruence on terms in whnf: same constant, free variable, or projection, or
        applications of equal functions to equal arguments.
        """
        match t, s:
            case Const(name1, universes1), Const(name2, universes2):
                return (
                    name1 == name2
                    and len(universes1) == len(universes2)
                    and all(map(level_equiv, universes1, universes2))
                )
            case FVar(), FVar():
                return t == s
            case Projection(type1, index1, struct1), Projection(type2, index2, struct2):
                return type1 == type2 and index1 == index2 and self.def_eq(struct1, struct2)
            case App(fn1, arg1), App(fn2, arg2):
                return self.def_eq(fn1, fn2) and self.def_eq(arg1, arg2)
            case _:
                return False

    def def_eq_args(self, t: Expr, s: Expr) -> bool:
        """
        `f a1 ... an =?= f b1 ... bn` because `ai =?= bi` for all `i`, and `f` has the same
        universe levels on both sides.
        """
        match t, s:
            case App(fn1, arg1), App(fn2, arg2):
                return self.def_eq(arg1, arg2) and self.def_eq_args(fn1, fn2)
            case _:
                return self.def_eq_stuck(t, s)

    def def_eq_eta(self, t: Expr, s: Expr) -> bool:
        """
        Eta: `f` is `fun x => f x`. To compare a lambda `t` with a non-lambda `s : (x : A) → B`,
        compare `t` with the eta expansion of `s`.
        """
        if not isinstance(t, Lambda) or isinstance(s, Lambda):
            return False
        s_type = self.whnf(self.infer_term(s))
        if not isinstance(s_type, Forall):
            return False
        # `s` has no loose bound variables, so `BVar(0)` refers to the new binder
        s_expanded = Lambda(
            s_type.var, s_type.binder_type, s_type.binder_info, App(s, BVar(0))
        )
        return self.def_eq(t, s_expanded)

    def def_eq_eta_struct(self, t: Expr, s: Expr) -> bool:
        """
        Structure eta: `p` is `S.mk p.1 ... p.n`. To compare `t` with a constructor application
        `s = S.mk params fields`, compare each field with the corresponding projection of `t`.
        """
        ctor = get_head(s)
        if not isinstance(ctor, Const):
            return False
        decl = self.env.constants.get(ctor.name)
        if not isinstance(decl, Constructor) or not self.is_structure(decl.inductive_name):
            return False

        # the projections of `t` only make sense if `t` is also of type `S params`
        s_type = self.infer_term(s)
        if not self.def_eq(self.infer_term(t), s_type):
            return False

        # if `S.mk` is partially applied, `s` and `t` are functions: apply both to fresh free
        # variables for the missing arguments, so that `S.mk` becomes fully applied
        while isinstance(s_type, Forall):
            fvar = self.new_free_variable(s_type.binder_type)
            t, s = App(t, fvar), App(s, fvar)
            s_type = instantiate(s_type.body, fvar)

        # `s` is now `S.mk params fields`: compare its fields, from the last one, with the
        # projections of `t`
        for i in reversed(range(decl.num_fields)):
            assert isinstance(s, App)
            if not self.def_eq(Projection(decl.inductive_name, i, t), s.arg):
                return False
            s = s.fn
        return True

    def def_eq_unit_like(self, t: Expr, s: Expr) -> bool:
        """
        A unit-like type has exactly one value, so any two terms of that type are equal.
        """
        t_type = self.whnf(self.infer_term(t))
        return self.is_unit_like(t_type) and self.def_eq(t_type, self.infer_term(s))

    def is_unit_like(self, type_: Expr) -> bool:
        """
        True iff `type_` is `A1 → ... → An → S params`, where `S` is a structure all of whose
        fields are proofs or are themselves unit-like (e.g. `Unit`, `True ∧ True`, `Nat → Unit`).
        """
        # look at the final codomain
        type_ = self.whnf(type_)
        while isinstance(type_, Forall):
            fvar = self.new_free_variable(type_.binder_type)
            type_ = self.whnf(instantiate(type_.body, fvar))

        struct = get_head(type_)
        if not isinstance(struct, Const) or not self.is_structure(struct.name):
            return False

        # the type of `S.mk params` is `(fields) → S params`: replace `S` with `S.mk` in `S params`
        inductive = self.env.get(struct.name)
        assert isinstance(inductive, Inductive)
        ctor = Const(inductive.constructor_names[0], struct.universes)
        ctor_type = self.whnf(self.infer_term(replace_fn(type_, get_num_args(type_), ctor)))
        while isinstance(ctor_type, Forall):
            field_type = ctor_type.binder_type
            if not self.is_prop(field_type) and not self.is_unit_like(field_type):
                return False
            fvar = self.new_free_variable(field_type)
            ctor_type = self.whnf(instantiate(ctor_type.body, fvar))
        return True

    def is_structure(self, name: Name) -> bool:
        """
        True iff `name` is a non-recursive structure: an inductive type with exactly one
        constructor and no indices, which does not refer to itself.
        """
        decl = self.env.constants.get(name)
        return (
            isinstance(decl, Inductive)
            and len(decl.constructor_names) == 1
            and decl.num_indices == 0
            and not decl.is_recursive
        )

    def whnf(self, expr: Expr) -> Expr:
        """
        Weak head normal form: reduce until the head of `expr` cannot be reduced any further,
        unfolding definitions one at a time.
        """
        expr = self.whnf_core(expr)
        value = self.reduce_nat(expr)
        if value is not None:
            return value
        unfolded = self.unfold_definition(expr)
        return expr if unfolded is None else self.whnf(unfolded)

    def reduce_nat(self, expr: Expr) -> Expr | None:
        """
        Compute `Nat.succ n` and the binary functions in `NAT_BINARY_OPS`, e.g. `Nat.add 2 3`,
        when their arguments reduce to literals. The result is a literal (or a `Bool` for the
        comparisons): this is much faster than unfolding the definitions, which would work on
        the unary representation `Nat.succ (Nat.succ ...)`.
        """
        match expr:
            case App(fn, arg) if fn == NAT_SUCC:
                n = nat_value(self.whnf(arg))
                return None if n is None else NatLiteral(n + 1)
            case App(App(Const(name, ()), arg1), arg2) if name in NAT_BINARY_OPS:
                n1 = nat_value(self.whnf(arg1))
                if n1 is None:
                    return None
                n2 = nat_value(self.whnf(arg2))
                if n2 is None:
                    return None
                result = NAT_BINARY_OPS[name](n1, n2)
                if isinstance(result, bool):
                    return BOOL_TRUE if result else BOOL_FALSE
                return NatLiteral(result)
            case _:
                return None

    def whnf_core(self, expr: Expr) -> Expr:
        """
        Weak head normal form, except that the head is never a definition unfolded by delta
        reduction (see `unfold_definition`). This lets `def_eq` choose what to unfold.
        """
        match expr:
            case MData(inner, _):
                # metadata is irrelevant for the kernel
                return self.whnf_core(inner)

            case Let(_, _, value, body, _):
                # zeta rule:
                # let x := value; body -> body[x := value]
                return self.whnf_core(instantiate(body, value))

            case App(fn, arg):
                # first reduce the function: for `f a b`, this means reducing `f a`
                fn = self.whnf_core(fn)
                if isinstance(fn, Lambda):
                    # beta rule:
                    # (lambda x, body) arg -> body[x := arg]
                    return self.whnf_core(instantiate(fn.body, arg))
                # iota rule: a recursor applied to a constructor
                expr = App(fn, arg)
                reduced = self.reduce_recursor(expr)
                if reduced is not None:
                    return self.whnf_core(reduced)
                return expr

            case Projection(type_name, index, struct):
                # proj: the structure must reduce to a constructor application `S.mk args`
                struct = self.whnf(struct)
                if isinstance(struct, StringLiteral):
                    struct = self.whnf(string_lit_to_constructor(struct.value))

                ctor = get_head(struct)
                if not isinstance(ctor, Const):
                    return expr
                decl = self.env.constants.get(ctor.name)
                if not isinstance(decl, Constructor) or decl.inductive_name != type_name:
                    return expr

                # the arguments of the constructor are the parameters of `S`, then its fields:
                # the field `index` is followed by `after` more arguments
                after = get_num_args(struct) - decl.num_params - index - 1
                if after < 0:
                    return expr  # partially applied constructor
                field = get_fn(struct, after)
                assert isinstance(field, App)
                return self.whnf_core(field.arg)

            case _:
                # everything else is already in whnf
                return expr

    def unfoldable(self, expr: Expr) -> Definition | Theorem | None:
        """
        The definition at the head of `expr`, if it can be unfolded. Only definitions and
        theorems have a value: axioms, opaque definitions, inductive types, constructors and
        recursors are stuck.
        """
        head = get_head(expr)
        if not isinstance(head, Const):
            return None
        decl = self.env.constants.get(head.name)
        if not isinstance(decl, (Definition, Theorem)):
            return None
        if len(head.universes) != len(decl.info.level_params):
            return None
        return decl

    def unfold_definition(self, expr: Expr) -> Expr | None:
        """
        Delta rule: replace the definition at the head of `expr` with its value.
        """
        decl = self.unfoldable(expr)
        if decl is None:
            return None
        head = get_head(expr)
        assert isinstance(head, Const)
        value = instantiate_universe_parameters(decl.value, decl.info.level_params, head.universes)
        return replace_fn(expr, get_num_args(expr), value)

    def reduce_recursor(self, expr: App) -> Expr | None:
        """
        Iota: a recursor applied to a constructor reduces with the rule for that constructor,

            I.rec params motives minors indices (c params fields) ~> rhs_c params motives minors fields

        where `rhs_c` abstracts over the arguments. Here `expr` must end with the major premise:
        any extra arguments are applied afterwards by `whnf`, as for any other application.
        """
        rec = get_head(expr)
        if not isinstance(rec, Const):
            return None
        decl = self.env.constants.get(rec.name)
        if isinstance(decl, Quot):
            return self.reduce_quot(decl, expr)
        if not isinstance(decl, Recursor) or len(rec.universes) != len(decl.info.level_params):
            return None
        num_before_indices = decl.num_params + decl.num_motives + decl.num_minors
        if get_num_args(expr) != num_before_indices + decl.num_indices + 1:
            return None

        # turn the major premise into a constructor application, if possible
        major = expr.arg
        if decl.is_k:
            major = self.to_constructor_when_k(decl, major)
        # a proof is not unfolded (like the official kernel): `to_constructor_when_k` and
        # `to_constructor_when_structure` are what make recursors on proofs reduce
        if not self.is_proof(major):
            major = self.whnf(major)
        if isinstance(major, NatLiteral):
            major = nat_lit_to_constructor(major.value)
        elif isinstance(major, StringLiteral):
            major = self.whnf(string_lit_to_constructor(major.value))
        else:
            major = self.to_constructor_when_structure(decl, major)

        ctor = get_head(major)
        rule = next(
            (r for r in decl.rules if isinstance(ctor, Const) and r.constructor_name == ctor.name),
            None,
        )
        if rule is None or get_num_args(major) < rule.num_fields:
            return None

        rhs = instantiate_universe_parameters(rule.rhs, decl.info.level_params, rec.universes)
        # `rhs params motives minors`: drop the indices and the major premise, replace `I.rec`
        rhs = replace_fn(get_fn(expr, decl.num_indices + 1), num_before_indices, rhs)
        # `rhs params motives minors fields`: the fields are the last arguments of the major premise
        return replace_fn(major, rule.num_fields, rhs)

    def to_constructor_when_k(self, rec: Recursor, major: Expr) -> Expr:
        """
        K-like reduction: if `I` is a proposition with a single constructor `c` without fields
        (e.g. `Eq`), any `h : I params indices` is, by proof irrelevance, `c params`, as long as
        `c params` has the same type. E.g. any `h : Eq a a` is `Eq.refl a`, so `Eq.rec` reduces
        on `h` even if `h` is not a constructor application, e.g. a variable.
        """
        major_type = self.whnf(self.infer_term(major))
        inductive = get_head(major_type)
        if not isinstance(inductive, Const) or inductive.name != major_inductive(rec):
            return major
        decl = self.env.get(inductive.name)
        assert isinstance(decl, Inductive)

        # `c params`: replace `I` with `c` in `I params indices`, without indices
        ctor = Const(decl.constructor_names[0], inductive.universes)
        ctor_app = replace_fn(get_fn(major_type, decl.num_indices), decl.num_params, ctor)
        # `h : Eq a b` is not `Eq.refl a`, unless `a` and `b` are equal
        if not self.def_eq(major_type, self.infer_term(ctor_app)):
            return major
        return ctor_app

    def to_constructor_when_structure(self, rec: Recursor, major: Expr) -> Expr:
        """
        Structure eta: if `major : S params` for a structure `S`, it is `S.mk params major.1 ...
        major.n`, so the recursor of `S` reduces even if `major` is not a constructor application.
        """
        name = major_inductive(rec)
        head = get_head(major)
        if not self.is_structure(name) or (
            isinstance(head, Const) and isinstance(self.env.constants.get(head.name), Constructor)
        ):
            return major
        major_type = self.whnf(self.infer_term(major))
        struct = get_head(major_type)
        if not isinstance(struct, Const) or struct.name != name:
            return major

        # a proposition which eliminates only into Prop (e.g. `Exists`) may have data fields,
        # which cannot be projected out of a proof. Such a recursor has no universe parameter
        # for the motive, unlike large eliminating ones
        decl = self.env.get(name)
        assert isinstance(decl, Inductive)
        if len(rec.info.level_params) == len(decl.info.level_params):
            return major

        # replace `S` with `S.mk` in `S params`, then add the fields
        ctor = self.env.get(decl.constructor_names[0])
        assert isinstance(ctor, Constructor)
        result = replace_fn(major_type, ctor.num_params, Const(ctor.info.name, struct.universes))
        for i in range(ctor.num_fields):
            result = App(result, Projection(name, i, major))
        return result

    def reduce_quot(self, decl: Quot, expr: App) -> Expr | None:
        """
        `Quot.lift f h (Quot.mk r a) ~> f a` and `Quot.ind h (Quot.mk r a) ~> h a`, where the
        implicit arguments come first: `Quot.lift {α} {r} {β} f h q`, `Quot.ind {α} {r} {β} h q`.
        As for recursors, `expr` must end with `q`.
        """
        match decl.kind, expr:
            case "lift", App(App(App(_, f), _), q) if get_num_args(expr) == 6:
                pass
            case "ind", App(App(_, f), q) if get_num_args(expr) == 5:
                pass
            case _:
                return None

        mk = self.whnf(q)
        mk_head = get_head(mk)
        if not isinstance(mk, App) or not isinstance(mk_head, Const) or get_num_args(mk) != 3:
            return None
        mk_decl = self.env.constants.get(mk_head.name)
        if not isinstance(mk_decl, Quot) or mk_decl.kind != "ctor":
            return None
        return App(f, mk.arg)
