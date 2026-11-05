from yalk.parser import ExportedDefinitions
from yalk.types import (
    Axiom, Constructor, Declaration, DeclarationInfo, Definition, Expr,
    Inductive, InductiveBlock, Level, Name, Opaque, Quot, Recursor, Sort, Theorem, Zero,
)
from loguru import logger

ConstantInfo = Axiom | Definition | Theorem | Opaque | Quot | Inductive | Constructor | Recursor

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
            case Axiom(info=info, is_unsafe=is_unsafe):
                assert not is_unsafe, "unsafe axioms are not supported"
                check_axiom(self, decl)
                self.constants[info.name] = decl
            case _:
                pass
                # raise NotImplementedError(f"checking {type(decl)} not implemented")


def check_axiom(env: Environment, axiom: Axiom) -> None:
    check_declaration_info(env, axiom.info)

def check_declaration_info(env: Environment, info: DeclarationInfo) -> None:
    # ensure that the universe parameters are unique
    ensure_parameters_unique(info.level_params)

    # ensure that the type does not have free variables
    if has_free_variables(info.declaration_type):
        raise KernelError(f"declaration type has free variables: {info.declaration_type}")

    # ensure that the type of the declaration type is a Sort _
    tc = TypeChecker(env)
    inferred_type = tc.infer_type(info.declaration_type)

class TypeChecker:
    def __init__(self, env: Environment) -> None:
        self.env = env

    def infer_type(self, term : Expr) -> Expr:
        return Sort(Zero())


def ensure_parameters_unique(parameters: tuple[Name, ...]) -> None:
    seen_names = set()
    for name in parameters:
        if name in seen_names:
            raise KernelError(f"duplicate level parameter: {name}")
        seen_names.add(name)

def has_free_variables(expr: Expr) -> bool:
    from yalk.types import App, FVar, Forall, Lambda, Let, Projection
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
            return (has_free_variables(binder_type) or
                    has_free_variables(value) or
                    has_free_variables(body))
        case Projection(struct=struct):
            return has_free_variables(struct)
        case _:
            return False