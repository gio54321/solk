from dataclasses import replace

from solk.levels import is_never_zero, is_zero, level_equiv, level_geq
from solk.environment import Environment, check_declaration_info
from solk.tc import TypeChecker
from solk.utils import (
    KernelError,
    UnsupportedError,
    consume_type_annotations,
    ensure_parameters_unique,
    erase_binder_names,
    instantiate,
    mentions_constant,
)
from solk.types import (
    Anon,
    App,
    BVar,
    Const,
    Constructor,
    DeclarationInfo,
    Expr,
    Forall,
    FVar,
    Inductive,
    InductiveBlock,
    Lambda,
    Let,
    Level,
    MData,
    Name,
    Param,
    Projection,
    RecursionRule,
    Recursor,
    Sort,
    StrName,
    Zero,
)


def check_inductive_block(env: Environment, block: InductiveBlock) -> None:
    InductiveBlockChecker(env, block).check()


class InductiveBlockChecker:
    def __init__(self, env: Environment, block: InductiveBlock) -> None:
        if len(block.types) == 0:
            raise KernelError("empty inductive block")
        self.env = env
        self.block = block
        self.types = block.types
        self.names = [t.info.name for t in block.types]

        # the universe parameters and the number of parameters are common to the whole block
        self.level_params = block.types[0].info.level_params
        self.levels = tuple(Param(p) for p in self.level_params)
        self.num_params = block.types[0].num_params

        # all the free variables used in this check live in a single type checker
        self.tc = TypeChecker(env, block.types[0].info)

        # set by `check_types`: a free variable for each parameter; for each type, the free
        # variables for its indices and the applications `I_j params` and `I_j params indices`;
        # the universe level `u` of `I_j params indices : Sort u`
        self.params: list[FVar] = []
        self.indices: list[list[FVar]] = []
        self.with_params: list[Expr] = []
        self.major_types: list[Expr] = []
        self.result_level: Level = Zero()

        # set by `check_constructors`: for each constructor `c`, its fields as free variables, the
        # application `c params fields`, and the indices of its result type `I_j params indices`
        self.fields: dict[Name, list[FVar]] = {}
        self.ctor_apps: dict[Name, Expr] = {}
        self.ctor_indices: dict[Name, list[Expr]] = {}

    def check(self) -> None:
        self.check_supported()
        ensure_parameters_unique(self.level_params)
        self.check_uniform_occurrences()
        self.check_types()
        self.add_types()
        self.check_constructors()
        self.add_constructors()
        self.add_recursors()

    def check_supported(self) -> None:
        """
        Reject unsafe and nested declarations, and check that the exported declarations are
        consistent with each other: same universe parameters and number of parameters, and
        exactly the constructors and recursors of the declared types, in order.
        """
        for t in self.types:
            if t.is_unsafe:
                raise KernelError(f"unsafe inductive type: {t.info.name}")
            if t.num_nested != 0:
                raise UnsupportedError(f"nested inductive types are not supported: {t.info.name}")
            if t.info.level_params != self.level_params or t.num_params != self.num_params:
                raise KernelError(f"mismatched (universe) parameters: {t.info.name}")
            if t.all_inductive_names != tuple(self.names):
                raise KernelError(f"mismatched mutual block: {t.info.name}")

        ctor_names = [n for t in self.types for n in t.constructor_names]
        if [c.info.name for c in self.block.constructors] != ctor_names:
            raise KernelError(f"constructors do not match the inductive types: {self.names}")
        rec_names = [StrName(n, "rec") for n in self.names]
        if [r.info.name for r in self.block.recursors] != rec_names:
            raise KernelError(f"recursors do not match the inductive types: {self.names}")

        for ctor in self.block.constructors:
            if ctor.is_unsafe:
                raise KernelError(f"unsafe constructor: {ctor.info.name}")
        for rec in self.block.recursors:
            if rec.is_unsafe:
                raise KernelError(f"unsafe recursor: {rec.info.name}")

    def check_uniform_occurrences(self) -> None:
        """
        Every occurrence of a type `I_j` of the block in a constructor type must be applied to
        (at least) the universe parameters and the parameters of the block, i.e. to the bound
        variables of the first `n` binders of the constructor type.

        This is checked syntactically, because the next checks look at constructor types up to
        `whnf`, which may erase an occurrence: `(fun _ => Unit) (I Nat)` reduces to `Unit`.
        """

        def check(expr: Expr, depth: int) -> None:
            # under `depth` binders, the parameters are `#(depth-1), ..., #(depth-n)`, so the only
            # valid occurrences are `I_j #(depth-1) ... #(depth-n)`
            if depth >= self.num_params:
                for name in self.names:
                    occurrence: Expr = Const(name, self.levels)
                    for i in range(self.num_params):
                        occurrence = App(occurrence, BVar(depth - 1 - i))
                    if expr == occurrence:
                        return
            # anything else must not be an occurrence of `I_j`: look for it in the subterms. In
            # `I_j params indices`, this finds the valid occurrence `I_j params` (and checks the
            # indices); in `I_j wrong_params`, it ends up at the constant `I_j` itself.
            match expr:
                case Const(name, _) if name in self.names:
                    raise KernelError(f"non-uniform occurrence of {name}")
                case App(fn, arg):
                    check(fn, depth)
                    check(arg, depth)
                case Lambda(_, binder_type, _, body) | Forall(_, binder_type, _, body):
                    check(binder_type, depth)
                    check(body, depth + 1)
                case Let(_, binder_type, value, body, _):
                    check(binder_type, depth)
                    check(value, depth)
                    check(body, depth + 1)
                case Projection(_, _, struct):
                    check(struct, depth)
                case MData(inner, _):
                    check(inner, depth)

        for ctor in self.block.constructors:
            check(ctor.info.declaration_type, 0)
    
    def check_types(self) -> None:
        """
        Check that each type is `(params) → (indices) → Sort u`, where the parameters and `u` are
        the same for all the types of the block.
        """
        for j, t in enumerate(self.types):
            check_declaration_info(self.env, t.info)
            if StrName(t.info.name, "rec") in self.env.constants:
                raise KernelError(f"already declared: {t.info.name}.rec")

            type_ = self.tc.whnf(t.info.declaration_type)
            i = 0
            indices: list[FVar] = []
            # `I_j params` and `I_j params indices`, built as the variables are introduced
            with_params: Expr = Const(t.info.name, self.levels)
            with_indices: Expr = with_params
            while isinstance(type_, Forall):
                if i < self.num_params:
                    if j == 0:
                        # the parameters of the first type become *the* parameters of the block
                        self.params.append(self.tc.new_free_variable(consume_type_annotations(type_.binder_type)))
                    elif not self.tc.def_eq(type_.binder_type, self.tc.type_of(self.params[i])):
                        raise KernelError(f"parameters of {t.info.name} do not match")
                    type_ = instantiate(type_.body, self.params[i])
                    with_params = with_indices = App(with_params, self.params[i])
                else:
                    index = self.tc.new_free_variable(consume_type_annotations(type_.binder_type))
                    indices.append(index)
                    type_ = instantiate(type_.body, index)
                    with_indices = App(with_indices, index)
                i += 1
                type_ = self.tc.whnf(type_)

            if i < self.num_params:
                raise KernelError(f"{t.info.name} has fewer than {self.num_params} parameters")
            if not isinstance(type_, Sort):
                raise KernelError(f"{t.info.name} is not a type former: {type_}")
            if j == 0:
                self.result_level = type_.level
            elif not level_equiv(type_.level, self.result_level):
                raise KernelError("mutual inductive types must live in the same universe")
            self.indices.append(indices)
            self.with_params.append(with_params)
            self.major_types.append(with_indices)

    def add_types(self) -> None:
        """
        Add the types to the environment, so that the constructors can refer to them.
        """
        # a block is recursive if some constructor argument mentions a type of the block, and
        # reflexive if one such argument is a function, e.g. `(Nat → I) → I`
        recursive = reflexive = False
        for ctor in self.block.constructors:
            type_ = ctor.info.declaration_type
            while isinstance(type_, Forall):
                if mentions_constant(type_.binder_type, self.names):
                    recursive = True
                    reflexive = reflexive or isinstance(type_.binder_type, Forall)
                type_ = type_.body

        for j, t in enumerate(self.types):
            derived = Inductive(
                info=t.info,
                num_params=self.num_params,
                num_indices=len(self.indices[j]),
                all_inductive_names=tuple(self.names),
                constructor_names=t.constructor_names,
                num_nested=0,
                is_recursive=recursive,
                is_unsafe=False,
                is_reflexive=reflexive,
            )
            if derived != t:
                raise KernelError(f"exported inductive type does not match: {t}")
            self.env.constants[t.info.name] = t

    def check_constructors(self) -> None:
        """
        Check that each constructor of `I_j` has type `(params) → (fields) → I_j params indices`
        where:
          * the parameters are the parameters of the block;
          * each field lives in a universe not larger than `I_j`'s (unless `I_j` is a `Prop`):
            otherwise `I_j : Type` could contain e.g. a `Type`, leading to Girard's paradox;
          * the types of the block occur only strictly positively in the fields (see
            `check_positivity`).
        """
        for j, t in enumerate(self.types):
            ctors = [c for c in self.block.constructors if c.info.name in t.constructor_names]
            for k, ctor in enumerate(ctors):
                name = ctor.info.name
                check_declaration_info(self.env, ctor.info)
                if ctor.info.level_params != self.level_params:
                    raise KernelError(f"mismatched universe parameters: {name}")

                type_ = ctor.info.declaration_type
                i = 0
                fields: list[FVar] = []
                # `c params fields`, built as the variables are introduced
                ctor_app: Expr = Const(name, self.levels)
                while isinstance(type_, Forall):
                    if i < self.num_params:
                        if not self.tc.def_eq(type_.binder_type, self.tc.type_of(self.params[i])):
                            raise KernelError(f"parameter {i} of {name} does not match")
                        type_ = instantiate(type_.body, self.params[i])
                        ctor_app = App(ctor_app, self.params[i])
                    else:
                        sort = self.tc.whnf(self.tc.infer_term(type_.binder_type))
                        if not isinstance(sort, Sort):
                            raise KernelError(f"argument {i} of {name} is not a type")
                        if not (
                            level_geq(self.result_level, sort.level)
                            or is_zero(self.result_level)
                        ):
                            raise KernelError(f"argument {i} of {name} lives in a universe too large")
                        self.check_positivity(type_.binder_type, name)
                        field = self.tc.new_free_variable(consume_type_annotations(type_.binder_type))
                        fields.append(field)
                        type_ = instantiate(type_.body, field)
                        ctor_app = App(ctor_app, field)
                    i += 1

                result = self.applied_type(type_)
                if result is None or result[0] != j:
                    raise KernelError(f"invalid result type for {name}: {type_}")

                derived = Constructor(
                    info=ctor.info,
                    inductive_name=t.info.name,
                    constructor_index=k,
                    num_params=self.num_params,
                    num_fields=len(fields),
                    is_unsafe=False,
                )
                if derived != ctor:
                    raise KernelError(f"exported constructor does not match: {ctor}")
                self.fields[name] = fields
                self.ctor_apps[name] = ctor_app
                self.ctor_indices[name] = result[1]

    def check_positivity(self, type_: Expr, ctor_name: Name) -> None:
        """
        The types of the block must occur strictly positively in the type of a field: the field
        is either non-recursive (no occurrence at all), or `(ys : Ys) → I_j params indices`, where
        the `Ys` do not mention the block. Otherwise, with e.g. `| mk : (I → False) → I`, one can
        prove `False`.
        """
        type_ = self.tc.whnf(type_)
        if not mentions_constant(type_, self.names):
            return
        if isinstance(type_, Forall):
            if mentions_constant(type_.binder_type, self.names):
                raise KernelError(f"non-positive occurrence of the block in {ctor_name}")
            y = self.tc.new_free_variable(consume_type_annotations(type_.binder_type))
            self.check_positivity(instantiate(type_.body, y), ctor_name)
        elif self.applied_type(type_) is None:
            raise KernelError(f"invalid occurrence of the block in {ctor_name}: {type_}")

    def add_constructors(self) -> None:
        # the constructors are added only after all of them are checked, so that a constructor
        # type cannot refer to another constructor
        for ctor in self.block.constructors:
            if ctor.info.name in self.env.constants:
                raise KernelError(f"already declared: {ctor.info.name}")
            self.env.constants[ctor.info.name] = ctor

    def add_recursors(self) -> None:
        """
        Derive the recursors of the block, check that they agree with the exported ones, and add
        them to the environment. All the recursors of a mutual block take the same arguments:

            I_j.rec params motives minors indices_j (t : I_j params indices_j) : motive_j indices_j t
        """
        elim_level = self.elimination_level()
        rec_level_params = self.level_params
        if isinstance(elim_level, Param):
            rec_level_params = (elim_level.name, *self.level_params)
        rec_levels = tuple(Param(p) for p in rec_level_params)

        # motive_j : (indices_j) → I_j params indices_j → Sort elim_level
        majors: list[FVar] = []
        motives: list[FVar] = []
        for j in range(len(self.types)):
            majors.append(self.tc.new_free_variable(self.major_types[j]))
            motive_type = self.tc.pi([*self.indices[j], majors[j]], Sort(elim_level))
            motives.append(self.tc.new_free_variable(motive_type))

        # one minor premise for each constructor, e.g. for `Vec.cons`:
        #   (a : α) → {n : Nat} → (t : Vec α n) → (t_ih : motive n t) → motive (n + 1) (Vec.cons a t)
        # with an induction hypothesis for each recursive field.
        minors: dict[Name, FVar] = {}
        recursive_fields: dict[Name, list[tuple[list[FVar], Expr, int, list[Expr]]]] = {}
        for ctor in self.block.constructors:
            name = ctor.info.name
            recursive_fields[name] = []
            ihs: list[FVar] = []
            for field in self.fields[name]:
                # a recursive field `x : (ys : Ys) → I_k params indices` has the induction
                # hypothesis `(ys : Ys) → motive_k indices (x ys)`
                recursive = self.as_recursive_field(field)
                if recursive is None:
                    continue
                ys, field_app, k, indices = recursive
                recursive_fields[name].append(recursive)
                ih_type: Expr = motives[k]
                for index in indices:
                    ih_type = App(ih_type, index)
                ih_type = App(ih_type, field_app)
                ihs.append(self.tc.new_free_variable(self.tc.pi(ys, ih_type)))

            # motive_j indices (c params fields)
            minor_type: Expr = motives[self.names.index(ctor.inductive_name)]
            for index in self.ctor_indices[name]:
                minor_type = App(minor_type, index)
            minor_type = App(minor_type, self.ctor_apps[name])
            minors[name] = self.tc.new_free_variable(self.tc.pi([*self.fields[name], *ihs], minor_type))

        is_k = (
            len(self.types) == 1
            and is_zero(self.result_level)
            and len(self.block.constructors) == 1
            and len(self.fields[self.block.constructors[0].info.name]) == 0
        )

        for j, (t, exported) in enumerate(zip(self.types, self.block.recursors)):
            rec_args = [*self.params, *motives, *minors.values()]
            # motive_j indices major
            rec_result: Expr = motives[j]
            for index in self.indices[j]:
                rec_result = App(rec_result, index)
            rec_result = App(rec_result, majors[j])
            rec_type = self.tc.pi([*rec_args, *self.indices[j], majors[j]], rec_result)

            # the rule for a constructor `c` applies the minor premise for `c` to the fields of
            # `c` and to the induction hypotheses, which are computed by recursive calls:
            #   I_j.rec params motives minors indices (c params fields)
            #     ~> minor_c fields (fun ys => I_k.rec params motives minors indices (x ys)) ...
            rules: list[RecursionRule] = []
            for ctor_name in t.constructor_names:
                fields = self.fields[ctor_name]
                minor_app: Expr = minors[ctor_name]
                for field in fields:
                    minor_app = App(minor_app, field)
                for ys, field_app, k, indices in recursive_fields[ctor_name]:
                    # fun ys => I_k.rec params motives minors indices (x ys)
                    rec_call: Expr = Const(StrName(self.names[k], "rec"), rec_levels)
                    for arg in [*rec_args, *indices, field_app]:
                        rec_call = App(rec_call, arg)
                    minor_app = App(minor_app, self.tc.lam(ys, rec_call))
                rhs = self.tc.lam([*rec_args, *fields], minor_app)
                rules.append(RecursionRule(ctor_name, len(fields), rhs))

            derived = Recursor(
                info=DeclarationInfo(StrName(t.info.name, "rec"), rec_level_params, rec_type),
                all_inductive_names=tuple(self.names),
                num_params=self.num_params,
                num_indices=len(self.indices[j]),
                num_motives=len(motives),
                num_minors=len(minors),
                rules=tuple(rules),
                is_k=is_k,
                is_unsafe=False,
            )
            if forget_binder_names(derived) != forget_binder_names(exported):
                raise KernelError(f"exported recursor does not match: {exported.info.name}")

        for rec in self.block.recursors:
            # e.g. a constructor `I.rec` would be replaced by the recursor
            if rec.info.name in self.env.constants:
                raise KernelError(f"already declared: {rec.info.name}")
            self.env.constants[rec.info.name] = rec

    def elimination_level(self) -> Level:
        """
        The universe the motives live in: a new universe parameter `u` (large elimination), or
        `0` if the recursors can only eliminate into `Prop`.

        Large elimination is restricted for inductive predicates (types in `Prop`): otherwise,
        one could e.g. define `def choose : Or A B → Bool` and distinguish two proofs of the same
        proposition, contradicting proof irrelevance. A predicate allows large elimination only
        if it is not mutual, and it has either no constructor, or a single constructor whose
        fields are all proofs, or appear in the indices of the result type (e.g. `Eq`).
        """
        if is_never_zero(self.result_level):
            only_prop = False  # not a predicate
        elif len(self.types) > 1 or len(self.block.constructors) > 1:
            only_prop = True
        elif len(self.block.constructors) == 0:
            only_prop = False
        else:
            ctor = self.block.constructors[0].info.name
            indices = self.ctor_indices[ctor]
            only_prop = any(
                field not in indices and not self.tc.is_proof(field) for field in self.fields[ctor]
            )
        if only_prop:
            return Zero()

        # a fresh universe parameter: `u`, or `u_1`, `u_2`, ... if `u` is taken
        name: Name = StrName(Anon(), "u")
        i = 1
        while name in self.level_params:
            name = StrName(Anon(), f"u_{i}")
            i += 1
        return Param(name)

    def as_recursive_field(
        self, field: FVar
    ) -> tuple[list[FVar], Expr, int, list[Expr]] | None:
        """
        If `field : (ys : Ys) → I_k params indices`, i.e. it is a recursive field, return
        `(ys, field ys, k, indices)`, otherwise None.
        """
        type_ = self.tc.whnf(self.tc.type_of(field))
        ys: list[FVar] = []
        field_app: Expr = field
        while isinstance(type_, Forall):
            y = self.tc.new_free_variable(consume_type_annotations(type_.binder_type))
            ys.append(y)
            field_app = App(field_app, y)
            type_ = self.tc.whnf(instantiate(type_.body, y))
        result = self.applied_type(type_)
        if result is None:
            return None
        k, indices = result
        return ys, field_app, k, indices

    def applied_type(
        self, type_: Expr, indices: tuple[Expr, ...] = ()
    ) -> tuple[int, list[Expr]] | None:
        """
        If `type_ indices` is `I_j params indices'`, i.e. the `j`-th type of the block applied to
        the parameters of the block and to indices not mentioning the block, return `j` and the
        indices `indices'`. Otherwise, return None.

        This peels one argument off `type_` at a time, until `I_j params` is left.
        """
        for j, with_params in enumerate(self.with_params):
            if (
                type_ == with_params
                and len(indices) == len(self.indices[j])
                and not any(mentions_constant(index, self.names) for index in indices)
            ):
                return j, list(indices)
        if isinstance(type_, App):
            return self.applied_type(type_.fn, (type_.arg, *indices))
        return None


def forget_binder_names(rec: Recursor) -> Recursor:
    """
    `rec` with all binder names and binder infos replaced by defaults, in its type and rules.
    """
    return replace(
        rec,
        info=replace(rec.info, declaration_type=erase_binder_names(rec.info.declaration_type)),
        rules=tuple(replace(rule, rhs=erase_binder_names(rule.rhs)) for rule in rec.rules),
    )
