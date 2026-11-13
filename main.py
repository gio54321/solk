from solk import parser
from solk.tc import Environment

def main() -> None:
    exported = parser.parse_exported_definitions("examples/simple_nat/axiom.ndjson")
    exported.pretty_print()
    env = Environment()
    env.add_all(exported)


if __name__ == "__main__":
    main()
