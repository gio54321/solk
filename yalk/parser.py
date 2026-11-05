from pathlib import Path
import json
from typing import Any, Callable, Dict, List, Optional, TypeVar, cast

from yalk.types import (
    Anon, App, Axiom, BinderInfo, BVar, Const, Constructor, Declaration,
    DeclarationInfo, Definition, DefinitionSafety, Expr, Forall, IMax,
    Inductive, InductiveBlock, Lambda, Let, Level, Max, MData, Meta, Name,
    NatLiteral, NumName, Opaque, Param, Projection, Quot, QuotKind,
    RecursionRule, Recursor, ReducibilityHints, RegularHint, Sort,
    StringLiteral, StrName, Succ, Theorem, Zero,
)

from yalk.pretty import pp_declaration, pp_name

SUPPORTED_FORMAT_MAJOR = "3"

T = TypeVar("T")
JSON = Dict[str, Any]


class ParseError(Exception):
    pass


def declaration_names(decl: Declaration) -> List[Name]:
    if isinstance(decl, InductiveBlock):
        return ([t.info.name for t in decl.types]
                + [c.info.name for c in decl.constructors]
                + [r.info.name for r in decl.recursors])
    return [decl.info.name]


class ExportedDefinitions:
    def __init__(self) -> None:
        self.meta: Optional[Meta] = None
        # the names list is initialized with the Anon name at index 0
        self.names: List[Name] = [Anon()]
        # the levels list is intialized with a Zero level, which is the lowest universe level
        self.levels: List[Level] = [Zero()]
        # expressions have no implicit entry: the first one has index 0
        self.exprs: List[Expr] = []
        # declarations, in the order in which they appear in the file
        # (dependencies come before their uses)
        self.declarations: List[Declaration] = []

    @staticmethod
    def _get(table: List[T], index: int, kind: str) -> T:
        if not isinstance(index, int) or not 0 <= index < len(table):
            raise ParseError(f"{kind} index {index} is out of bounds (have {len(table)})")
        return table[index]

    @staticmethod
    def _add(table: List[T], index: int, value: T, kind: str) -> None:
        if index != len(table):
            raise ParseError(f"{kind} index {index} is not sequential (expected {len(table)})")
        table.append(value)

    def set_meta(self, meta: Meta) -> None:
        if self.meta is not None:
            raise ParseError("meta information has already been set")
        self.meta = meta

    def get_name(self, index: int) -> Name:
        return self._get(self.names, index, "name")

    def add_name(self, index: int, name: Name) -> None:
        self._add(self.names, index, name, "name")

    def get_level(self, index: int) -> Level:
        return self._get(self.levels, index, "level")

    def add_level(self, index: int, level: Level) -> None:
        self._add(self.levels, index, level, "level")

    def get_expr(self, index: int) -> Expr:
        return self._get(self.exprs, index, "expr")

    def add_expr(self, index: int, expr: Expr) -> None:
        self._add(self.exprs, index, expr, "expr")

    def add_declaration(self, decl: Declaration) -> None:
        self.declarations.append(decl)

    def pretty_print(self) -> None:
        print(self.pretty())

    def pretty(self, summary: bool = False) -> str:
        """
        Pretty print the whole export: a summary of the tables followed by
        every declaration (only their names with `summary`).
        """
        lines = ["Exported Definitions:"]
        if self.meta:
            lines.append(f"Meta: {self.meta}")
        lines.append(f"Total Names: {len(self.names)}")
        lines.append(f"Total Levels: {len(self.levels)}")
        lines.append(f"Total Exprs: {len(self.exprs)}")
        lines.append(f"Total Declarations: {len(self.declarations)}")
        if summary:
            for decl in self.declarations:
                names = ", ".join(pp_name(n) for n in declaration_names(decl))
                lines.append(f"  {type(decl).__name__}: {names}")
            return "\n".join(lines)
        for decl in self.declarations:
            lines.append("")
            lines.append(pp_declaration(decl))
        return "\n".join(lines)


class _Parser:
    def __init__(self) -> None:
        self.out = ExportedDefinitions()
        self.decl_parsers: Dict[str, Callable[[JSON], Declaration]] = {
            "axiom": self.parse_axiom,
            "def": self.parse_definition,
            "thm": self.parse_theorem,
            "opaque": self.parse_opaque,
            "quot": self.parse_quot,
            "inductive": self.parse_inductive,
        }

    # -- helpers -------------------------------------------------------------

    def name(self, i: int) -> Name:
        return self.out.get_name(i)

    def names(self, xs: List[int]) -> tuple[Name, ...]:
        return tuple(self.out.get_name(i) for i in xs)

    def level(self, i: int) -> Level:
        return self.out.get_level(i)

    def expr(self, i: int) -> Expr:
        return self.out.get_expr(i)

    def parse_line(self, data: JSON) -> None:
        if "in" in data:
            self.out.add_name(data["in"], self.parse_name(data))
        elif "il" in data:
            self.out.add_level(data["il"], self.parse_level(data))
        elif "ie" in data:
            self.out.add_expr(data["ie"], self.parse_expr(data))
        elif "meta" in data:
            self.out.set_meta(self.parse_meta(data["meta"]))
        else:
            if len(data) != 1:
                raise ParseError(f"unrecognized object with keys {sorted(data)}")
            (kind, body), = data.items()
            parse = self.decl_parsers.get(kind)
            if parse is None:
                raise ParseError(f"unknown declaration kind {kind!r}")
            self.out.add_declaration(parse(body))

    def parse_meta(self, m: JSON) -> Meta:
        version = str(m["format"]["version"])
        if version.split(".")[0] != SUPPORTED_FORMAT_MAJOR:
            raise ParseError(f"unsupported export format version {version}")
        return Meta(exporter=m["exporter"], format=m["format"], lean=m["lean"])

    def parse_name(self, data: JSON) -> Name:
        if "str" in data:
            s = data["str"]
            return StrName(pre=self.name(s["pre"]), name=s["str"])
        if "num" in data:
            n = data["num"]
            return NumName(pre=self.name(n["pre"]), name=n["i"])
        raise ParseError(f"unknown name kind with keys {sorted(data)}")

    def parse_level(self, data: JSON) -> Level:
        if "succ" in data:
            return Succ(pred=self.level(data["succ"]))
        if "max" in data:
            left, right = data["max"]
            return Max(left=self.level(left), right=self.level(right))
        if "imax" in data:
            left, right = data["imax"]
            return IMax(left=self.level(left), right=self.level(right))
        if "param" in data:
            return Param(name=self.name(data["param"]))
        raise ParseError(f"unknown level kind with keys {sorted(data)}")

    @staticmethod
    def binder_info(b: str) -> BinderInfo:
        if b not in ("default", "implicit", "strictImplicit", "instImplicit"):
            raise ParseError(f"unknown binder info {b!r}")
        return cast(BinderInfo, b)

    def parse_expr(self, data: JSON) -> Expr:
        if "bvar" in data:
            return BVar(index=data["bvar"])
        if "sort" in data:
            return Sort(level=self.level(data["sort"]))
        if "const" in data:
            c = data["const"]
            return Const(name=self.name(c["name"]),
                         universes=tuple(self.level(u) for u in c["us"]))
        if "app" in data:
            a = data["app"]
            return App(fn=self.expr(a["fn"]), arg=self.expr(a["arg"]))
        if "lam" in data:
            b = data["lam"]
            return Lambda(var=self.name(b["name"]), binder_type=self.expr(b["type"]),
                          binder_info=self.binder_info(b["binderInfo"]),
                          body=self.expr(b["body"]))
        if "forallE" in data:
            b = data["forallE"]
            return Forall(var=self.name(b["name"]), binder_type=self.expr(b["type"]),
                          binder_info=self.binder_info(b["binderInfo"]),
                          body=self.expr(b["body"]))
        if "letE" in data:
            b = data["letE"]
            return Let(var=self.name(b["name"]), binder_type=self.expr(b["type"]),
                       value=self.expr(b["value"]), body=self.expr(b["body"]),
                       nondep=bool(b.get("nondep", False)))
        if "proj" in data:
            p = data["proj"]
            return Projection(type_name=self.name(p["typeName"]), index=p["idx"],
                              struct=self.expr(p["struct"]))
        if "natVal" in data:
            # nat literals are serialized as strings since they are unbounded
            return NatLiteral(value=int(data["natVal"]))
        if "strVal" in data:
            return StringLiteral(value=data["strVal"])
        if "mdata" in data:
            m = data["mdata"]
            return MData(expr=self.expr(m["expr"]), data=m["data"])
        raise ParseError(f"unknown expression kind with keys {sorted(data)}")

    def info(self, d: JSON) -> DeclarationInfo:
        return DeclarationInfo(name=self.name(d["name"]),
                               level_params=self.names(d["levelParams"]),
                               declaration_type=self.expr(d["type"]))

    def parse_axiom(self, d: JSON) -> Axiom:
        return Axiom(info=self.info(d), is_unsafe=d["isUnsafe"])

    @staticmethod
    def hints(h: Any) -> ReducibilityHints:
        if h == "opaque" or h == "abbrev":
            return cast(ReducibilityHints, h)
        if isinstance(h, dict) and "regular" in h:
            return RegularHint(height=h["regular"])
        raise ParseError(f"unknown reducibility hints {h!r}")

    @staticmethod
    def safety(s: str) -> DefinitionSafety:
        if s not in ("unsafe", "safe", "partial"):
            raise ParseError(f"unknown definition safety {s!r}")
        return cast(DefinitionSafety, s)

    def parse_definition(self, d: JSON) -> Definition:
        return Definition(info=self.info(d), value=self.expr(d["value"]),
                          hints=self.hints(d["hints"]), safety=self.safety(d["safety"]),
                          all_names=self.names(d["all"]))

    def parse_theorem(self, d: JSON) -> Theorem:
        return Theorem(info=self.info(d), value=self.expr(d["value"]),
                       all_names=self.names(d["all"]))

    def parse_opaque(self, d: JSON) -> Opaque:
        return Opaque(info=self.info(d), value=self.expr(d["value"]),
                      is_unsafe=d["isUnsafe"], all_names=self.names(d["all"]))

    def parse_quot(self, d: JSON) -> Quot:
        kind = d["kind"]
        if kind not in ("type", "ctor", "lift", "ind"):
            raise ParseError(f"unknown quot kind {kind!r}")
        return Quot(info=self.info(d), kind=cast(QuotKind, kind))

    def parse_inductive_type(self, d: JSON) -> Inductive:
        return Inductive(info=self.info(d), num_params=d["numParams"],
                         num_indices=d["numIndices"],
                         all_inductive_names=self.names(d["all"]),
                         constructor_names=self.names(d["ctors"]),
                         num_nested=d["numNested"], is_recursive=d["isRec"],
                         is_unsafe=d["isUnsafe"], is_reflexive=d["isReflexive"])

    def parse_constructor(self, d: JSON) -> Constructor:
        return Constructor(info=self.info(d), inductive_name=self.name(d["induct"]),
                           constructor_index=d["cidx"], num_params=d["numParams"],
                           num_fields=d["numFields"], is_unsafe=d["isUnsafe"])

    def parse_recursor(self, d: JSON) -> Recursor:
        rules = tuple(
            RecursionRule(constructor_name=self.name(r["ctor"]),
                          num_fields=r["nfields"], rhs=self.expr(r["rhs"]))
            for r in d["rules"]
        )
        return Recursor(info=self.info(d), all_inductive_names=self.names(d["all"]),
                        num_params=d["numParams"], num_indices=d["numIndices"],
                        num_motives=d["numMotives"], num_minors=d["numMinors"],
                        rules=rules, is_k=d["k"], is_unsafe=d["isUnsafe"])

    def parse_inductive(self, d: JSON) -> InductiveBlock:
        return InductiveBlock(
            types=tuple(self.parse_inductive_type(t) for t in d["types"]),
            constructors=tuple(self.parse_constructor(c) for c in d["ctors"]),
            recursors=tuple(self.parse_recursor(r) for r in d["recs"]),
        )


def parse_exported_definitions(path: str | Path) -> ExportedDefinitions:
    parser = _Parser()
    with open(path, "r") as f:
        for lineno, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                parser.parse_line(json.loads(line))
            except ParseError as e:
                raise ParseError(f"{path}:{lineno}: {e}") from None
            except (KeyError, TypeError, ValueError) as e:
                raise ParseError(f"{path}:{lineno}: malformed object: {e!r}") from e
    if parser.out.meta is None:
        raise ParseError(f"{path}: missing meta object")
    return parser.out
