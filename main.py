from yalk import parser

def main() -> None:
    exported = parser.parse_exported_definitions("examples/simple_nat.ndjson")
    exported.pretty_print()


if __name__ == "__main__":
    main()
