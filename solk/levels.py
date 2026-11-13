from solk.types import IMax, Level, Max, Name, Param, Succ, Zero


def is_zero(level: Level) -> bool:
    """
    True iff `level` is zero, whatever the values of its universe parameters.
    """
    match level:
        case Zero():
            return True
        case Succ():
            return False
        case Param():
            return False
        case Max(left, right):
            return is_zero(left) and is_zero(right)
        case IMax(left, right):
            return is_zero(right)


def is_never_zero(level: Level) -> bool:
    """
    True iff `level` is not zero, whatever the values of its universe parameters.
    """
    match level:
        case Zero() | Param():
            return False
        case Succ():
            return True
        case Max(left, right):
            return is_never_zero(left) or is_never_zero(right)
        case IMax(_, right):
            return is_never_zero(right)


def level_geq(l1: Level, l2: Level) -> bool:
    """
    True iff `l1 >= l2` for every assignment of natural numbers to the universe parameters.

    1. If some `imax a b` is undecided, i.e. `b` might or might not be zero depending on the
       parameters, pick a parameter `p` that decides it and check both cases, `p := 0` and
       `p := p + 1`. In both cases, `p` can no longer decide whether `b` is zero.
    2. Without undecided `imax`, a level is just a maximum of terms `p + k` and constants `k`.
       Then `l1 >= l2` iff every term of `l2` is dominated by a single term of `l1`:
         * `p + k2` is dominated by `p + k1` with `k1 >= k2` (take `p` large and the others 0);
         * `k2` is dominated by any term `_ + k1` with `k1 >= k2` (take all parameters 0).
    """
    param = undecided_imax_parameter(l1) or undecided_imax_parameter(l2)
    if param is not None:
        return all(
            level_geq(
                instantiate_level(l1, (param,), (value,)),
                instantiate_level(l2, (param,), (value,)),
            )
            for value in (Zero(), Succ(Param(param)))
        )

    def terms(level: Level) -> list[tuple[Name | None, int]]:
        # the terms `p + k` (or `k`, with `p` None) whose maximum is `level`
        match level:
            case Zero():
                return [(None, 0)]
            case Param(name):
                return [(name, 0)]
            case Succ(pred):
                return [(p, k + 1) for p, k in terms(pred)]
            case Max(left, right):
                return terms(left) + terms(right)
            case IMax(left, right):
                # not undecided, so `right` is either always zero or never zero
                if is_zero(right):
                    return [(None, 0)]
                return terms(left) + terms(right)

    return all(
        any(k1 >= k2 and (p1 == p2 or p2 is None) for p1, k1 in terms(l1))
        for p2, k2 in terms(l2)
    )


def level_equiv(l1: Level, l2: Level) -> bool:
    """
    True iff `l1` and `l2` denote the same universe for every assignment of the parameters.
    """
    return level_geq(l1, l2) and level_geq(l2, l1)


def undecided_imax_parameter(level: Level) -> Name | None:
    """
    If `level` contains an `imax a b` where `b` may or may not be zero, return a parameter on
    which this depends (one occurring in `b` outside of any `succ` and of the left side of an
    `imax`). Otherwise return None.
    """
    def deciding_parameter(level: Level) -> Name | None:
        match level:
            case Param(name):
                return name
            case Max(left, right):
                return deciding_parameter(left) or deciding_parameter(right)
            case IMax(_, right):
                return deciding_parameter(right)
            case _:
                return None

    match level:
        case Succ(pred):
            return undecided_imax_parameter(pred)
        case Max(left, right):
            return undecided_imax_parameter(left) or undecided_imax_parameter(right)
        case IMax(left, right):
            if not is_never_zero(right) and not is_zero(right):
                return deciding_parameter(right)
            return undecided_imax_parameter(left) or undecided_imax_parameter(right)
        case _:
            return None


def instantiate_level(
    level: Level, parameters: tuple[Name, ...], universes: tuple[Level, ...]
) -> Level:
    match level:
        case Zero():
            return Zero()
        case Succ(pred=pred):
            return Succ(
                instantiate_level(pred, parameters, universes)
            )
        case Param(name=name):
            for param, universe in zip(parameters, universes):
                if name == param:
                    return universe
            return Param(name)
        case Max(left=left, right=right):
            return Max(
                instantiate_level(left, parameters, universes),
                instantiate_level(right, parameters, universes),
            )
        case IMax(left=left, right=right):
            return IMax(
                instantiate_level(left, parameters, universes),
                instantiate_level(right, parameters, universes),
            )


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
