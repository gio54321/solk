from __future__ import annotations
from typing import Any, Dict, Literal
from dataclasses import dataclass, field

@dataclass(frozen=True)
class Meta:
    """
    Meta information about the exported file
    """
    exporter: Dict[str, Any]
    format: Dict[str, Any]
    lean: Dict[str, Any]

@dataclass(frozen=True)
class Anon:
    """
    A placeholder for an empty name, used to represent the absence of a name.
    """
    pass

@dataclass(frozen=True)
class StrName:
    # previous name in the linked list of names
    pre: Name
    # name string
    name: str

@dataclass(frozen=True)
class NumName:
    # previous name in the linked list of names
    pre: Name
    # name number
    name: int

Name = Anon | StrName | NumName

@dataclass(frozen=True)
class Zero:
    """
    The lowest universe
    """
    pass

@dataclass(frozen=True)
class Succ:
    """
    Successor of a universe
    """
    pred: Level

@dataclass(frozen=True)
class Max:
    """
    Lowest upper bound of two universes
    """
    left: Level
    right: Level

@dataclass(frozen=True)
class IMax:
    """
    Defined as Max(l, r) if r != Zero else Zero
    """
    left: Level
    right: Level

@dataclass(frozen=True)
class Param:
    """
    A parameterized universe, used for polymorphic definitions
    """
    name: Name

Level = Zero | Succ | Param | Max | IMax

BinderInfo = Literal["default", "implicit", "strictImplicit", "instImplicit"]

@dataclass(frozen=True)
class BVar:
    """
    Bound variable, indexed by its De Bruijn index
    """
    index: int

@dataclass(frozen=True)
class FVar:
    """
    Free variable, identified by its unique name. It carries its type, which is not part of its
    identity. Never produced by the exporter; used by the type checker.
    """
    name: str
    type: Expr = field(compare=False, repr=False)

@dataclass(frozen=True)
class Const:
    """
    A constant name applied to a list of universes
    """
    name: Name
    universes: tuple[Level, ...]

@dataclass(frozen=True)
class Sort:
    """
    A sort is a universe level
    """
    level: Level

@dataclass(frozen=True)
class App:
    """
    Application of a function to one argument
    """
    fn: Expr
    arg: Expr

@dataclass(frozen=True)
class Lambda:
    """
    Lambda abstraction
    """
    var: Name
    binder_type: Expr
    binder_info: BinderInfo
    body: Expr

@dataclass(frozen=True)
class Forall:
    """
    Pi abstraction
    """
    var: Name
    binder_type: Expr
    binder_info: BinderInfo
    body: Expr

@dataclass(frozen=True)
class Let:
    """
    Let binding
    """
    var: Name
    binder_type: Expr
    value: Expr
    body: Expr
    # true if the body does not depend on the value (`have`)
    nondep: bool

@dataclass(frozen=True)
class Projection:
    """
    Projection of the `index`-th field out of `struct`, a term whose type is
    the structure `type_name`
    """
    type_name: Name
    index: int
    struct: Expr

@dataclass(frozen=True)
class NatLiteral:
    """
    Natural number literal
    """
    value: int

@dataclass(frozen=True)
class StringLiteral:
    """
    String literal
    """
    value: str

@dataclass(frozen=True)
class MData:
    """
    Expression annotated with metadata (irrelevant for type checking)
    """
    expr: Expr
    data: Dict[str, Any]

LiteralExpr = NatLiteral | StringLiteral
Expr = BVar | FVar | Const | Sort | App | Lambda | Forall | Let | Projection | LiteralExpr | MData

@dataclass(frozen=True)
class DeclarationInfo:
    name: Name
    # names of the universe parameters the declaration is polymorphic over
    level_params: tuple[Name, ...]
    declaration_type: Expr

@dataclass(frozen=True)
class Axiom:
    info: DeclarationInfo
    is_unsafe: bool

@dataclass(frozen=True)
class RegularHint:
    """
    Reducibility hint of a regular definition: the definitional height
    """
    height: int

ReducibilityHints = Literal["opaque", "abbrev"] | RegularHint
DefinitionSafety = Literal["unsafe", "safe", "partial"]

@dataclass(frozen=True)
class Definition:
    info: DeclarationInfo
    value: Expr
    hints: ReducibilityHints
    safety: DefinitionSafety
    # names of all the definitions in the mutual block, including this one
    all_names: tuple[Name, ...]

@dataclass(frozen=True)
class Theorem:
    info: DeclarationInfo
    value: Expr
    all_names: tuple[Name, ...]

@dataclass(frozen=True)
class Opaque:
    info: DeclarationInfo
    value: Expr
    is_unsafe: bool
    all_names: tuple[Name, ...]

QuotKind = Literal["type", "ctor", "lift", "ind"]

@dataclass(frozen=True)
class Quot:
    info: DeclarationInfo
    kind: QuotKind

@dataclass(frozen=True)
class Inductive:
    info: DeclarationInfo
    num_params: int
    num_indices: int
    # the name of all the inductive types in the mutual block, including this one
    all_inductive_names: tuple[Name, ...]
    # the name of all the constructors for this type only
    constructor_names: tuple[Name, ...]
    num_nested: int
    is_recursive: bool
    is_unsafe: bool
    is_reflexive: bool

@dataclass(frozen=True)
class Constructor:
    info: DeclarationInfo
    # the inductive type this constructor belongs to
    inductive_name: Name
    # index of the constructor within its inductive type
    constructor_index: int
    num_params: int
    num_fields: int
    is_unsafe: bool

@dataclass(frozen=True)
class RecursionRule:
    constructor_name: Name
    # number of fields of the constructor (its arguments after the params)
    num_fields: int
    # the right-hand side of the iota reduction rule; a lambda abstracting
    # over params, motives, minors and the constructor fields
    rhs: Expr

@dataclass(frozen=True)
class Recursor:
    info: DeclarationInfo
    all_inductive_names: tuple[Name, ...]
    num_params: int
    num_indices: int
    num_motives: int
    num_minors: int
    rules: tuple[RecursionRule, ...]
    is_k: bool
    is_unsafe: bool

@dataclass(frozen=True)
class InductiveBlock:
    """
    A (possibly mutual) inductive declaration, grouped as the kernel checks it:
    the types together with their constructors and the generated recursors.
    """
    types: tuple[Inductive, ...]
    constructors: tuple[Constructor, ...]
    recursors: tuple[Recursor, ...]

Declaration = Axiom | Definition | Theorem | Opaque | Quot | InductiveBlock
