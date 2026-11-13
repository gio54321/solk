from solk.levels import is_zero
from solk.parser import ExportedDefinitions
from solk.tc import TypeChecker
from solk.types import (
    Axiom,
    Constructor,
    Declaration,
    DeclarationInfo,
    Definition,
    Expr,
    Inductive,
    InductiveBlock,
    Name,
    Opaque,
    Quot,
    Recursor,
    Sort,
    Theorem,
)
from solk.utils import KernelError, ensure_parameters_unique, has_free_variables


ConstantInfo = (
    Axiom | Definition | Theorem | Opaque | Quot | Inductive | Constructor | Recursor
)


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
            case InductiveBlock():
                # imported here because `inductive.py` itself uses `check_declaration_info` and
                # `Environment` from this file. The types, constructors and recursors are added
                # to the environment in stages, as they are checked.
                from solk.inductive import check_inductive_block

                check_inductive_block(self, decl)
                return
            case Quot():
                # imported here for the same reason as `inductive.py`
                from solk.quot import check_quot

                check_quot(self, decl)
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
    if not is_zero(sort.level):
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
