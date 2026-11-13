from solk.environment import Environment, check_declaration_info
from solk.tc import TypeChecker
from solk.types import (
    Anon,
    App,
    Const,
    Expr,
    Forall,
    Inductive,
    Name,
    Param,
    Quot,
    Sort,
    Zero,
)
from solk.utils import KernelError, erase_binder_names, mk_name


def check_quot(env: Environment, quot: Quot) -> None:
    """
    The quotient type `Quot r` and its operations are built into the kernel: `Quot.lift` and
    `Quot.ind` reduce on `Quot.mk` (see `reduce_quot`). So their types must be exactly:

        Quot.{u} {α : Sort u} (r : α → α → Prop) : Sort u
        Quot.mk.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Quot r
        Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
          (∀ a b : α, r a b → f a = f b) → Quot r → β
        Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
          (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
    """
    check_declaration_info(env, quot.info)
    if quot.kind == "type":
        check_eq(env)

    tc = TypeChecker(env)
    u, v = Param(mk_name("u")), Param(mk_name("v"))
    prop = Sort(Zero())
    alpha = tc.new_free_variable(Sort(u))
    r = tc.new_free_variable(
        Forall(Anon(), alpha, "default", Forall(Anon(), alpha, "default", prop))
    )
    quot_r = App(App(Const(mk_name("Quot"), (u,)), alpha), r)
    a = tc.new_free_variable(alpha)
    b = tc.new_free_variable(alpha)

    expected: tuple[Name, tuple[Param, ...], Expr]
    match quot.kind:
        case "type":
            expected = (mk_name("Quot"), (u,), tc.pi([alpha, r], Sort(u)))
        case "ctor":
            expected = (mk_name("Quot", "mk"), (u,), tc.pi([alpha, r, a], quot_r))
        case "lift":
            beta = tc.new_free_variable(Sort(v))
            f = tc.new_free_variable(Forall(Anon(), alpha, "default", beta))
            f_a_eq_f_b = App(App(App(Const(mk_name("Eq"), (v,)), beta), App(f, a)), App(f, b))
            respects_r = tc.pi([a, b], Forall(Anon(), App(App(r, a), b), "default", f_a_eq_f_b))
            lift_type = tc.pi(
                [alpha, r, beta, f],
                Forall(Anon(), respects_r, "default", Forall(Anon(), quot_r, "default", beta)),
            )
            expected = (mk_name("Quot", "lift"), (u, v), lift_type)
        case "ind":
            motive = tc.new_free_variable(Forall(Anon(), quot_r, "default", prop))
            q = tc.new_free_variable(quot_r)
            mk_a = App(App(App(Const(mk_name("Quot", "mk"), (u,)), alpha), r), a)
            all_mk = tc.pi([a], App(motive, mk_a))
            all_q = tc.pi([q], App(motive, q))
            ind_type = tc.pi([alpha, r, motive], Forall(Anon(), all_mk, "default", all_q))
            expected = (mk_name("Quot", "ind"), (u,), ind_type)

    name, level_params, type_ = expected
    if (
        quot.info.name != name
        or quot.info.level_params != tuple(p.name for p in level_params)
        or erase_binder_names(quot.info.declaration_type) != erase_binder_names(type_)
    ):
        raise KernelError(f"unexpected quotient declaration: {quot.info.name}")


def check_eq(env: Environment) -> None:
    """
    `Quot.lift` mentions `Eq`, which must then be the usual equality:

        inductive Eq.{u} {α : Sort u} : α → α → Prop
          | refl (a : α) : Eq a a
    """
    eq = env.get(mk_name("Eq"))
    if (
        not isinstance(eq, Inductive)
        or len(eq.info.level_params) != 1
        or len(eq.constructor_names) != 1
    ):
        raise KernelError("unexpected Eq type")
    refl = env.get(eq.constructor_names[0])

    tc = TypeChecker(env)
    u = Param(eq.info.level_params[0])
    alpha = tc.new_free_variable(Sort(u))
    a = tc.new_free_variable(alpha)
    eq_type = tc.pi(
        [alpha], Forall(Anon(), alpha, "default", Forall(Anon(), alpha, "default", Sort(Zero())))
    )
    refl_type = tc.pi([alpha, a], App(App(App(Const(eq.info.name, (u,)), alpha), a), a))
    if erase_binder_names(eq.info.declaration_type) != erase_binder_names(eq_type) or (
        erase_binder_names(refl.info.declaration_type) != erase_binder_names(refl_type)
    ):
        raise KernelError("unexpected Eq type")
