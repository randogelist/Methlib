"""Strict axiom-name parser from pinned native audit verifier.
Source: NSE---MAXWELL---GR---QFT@9f5500cd5dadc351ab3ec98db09dccaa9a22eb25/Auxillary/scripts/verify_audit.py
"""
import re

AXIOM_NAME = re.compile(
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
    r"(?:\.\{(?P<universes>[^{}]+)\})?\Z"
)

UNIVERSE_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[()+,]")

def split_axiom_list(text: str) -> list[str]:
    """Split declaration entries, preserving commas inside universe braces."""
    if not text.strip():
        return []
    result: list[str] = []
    depth = 0
    start = 0
    for index, char in enumerate(text):
        if char == "{":
            depth += 1
            if depth > 1:
                raise ValueError("Nested braces in an axiom universe suffix.")
        elif char == "}":
            depth -= 1
            if depth < 0:
                raise ValueError("Unbalanced braces in an axiom record.")
        elif char == "," and depth == 0:
            result.append(text[start:index].strip())
            start = index + 1
    if depth:
        raise ValueError("Unbalanced braces in an axiom record.")
    result.append(text[start:].strip())
    if any(not item for item in result):
        raise ValueError("Empty declaration entry in an axiom record.")
    return result

def validate_universes(text: str) -> None:
    """Recognize universe parameters, numerals, max/imax, and successors.

    Unsupported or malformed renderings fail closed. No declaration-name text
    outside the terminal universe suffix is discarded.
    """
    tokens: list[str] = []
    end = 0
    for match in UNIVERSE_TOKEN.finditer(text):
        if text[end:match.start()].strip():
            raise ValueError(f"Invalid universe-instantiation suffix: {text!r}")
        tokens.append(match.group())
        end = match.end()
    if text[end:].strip() or not tokens:
        raise ValueError(f"Invalid universe-instantiation suffix: {text!r}")
    position = 0

    def level(depth: int = 0) -> None:
        nonlocal position
        if depth > 32 or position >= len(tokens):
            raise ValueError(f"Malformed universe expression: {text!r}")
        token = tokens[position]
        position += 1
        if token in {"max", "imax"}:
            level(depth + 1)
            level(depth + 1)
        elif token == "(":
            level(depth + 1)
            if position >= len(tokens) or tokens[position] != ")":
                raise ValueError(f"Unclosed universe expression: {text!r}")
            position += 1
        elif token in {")", "+", ","}:
            raise ValueError(f"Malformed universe expression: {text!r}")
        while position < len(tokens) and tokens[position] == "+":
            position += 1
            if position >= len(tokens) or not tokens[position].isdigit():
                raise ValueError(f"Invalid universe successor: {text!r}")
            position += 1

    level()
    while position < len(tokens):
        if tokens[position] != ",":
            raise ValueError(f"Unexpected universe token: {text!r}")
        position += 1
        level()

def normalize_axiom_name(rendered: str) -> str:
    """Remove only a well-formed terminal .{...} universe instantiation."""
    match = AXIOM_NAME.fullmatch(rendered)
    if match is None:
        raise ValueError(f"Malformed rendered axiom name: {rendered!r}")
    universes = match.group("universes")
    if universes is not None:
        validate_universes(universes)
    return match.group("name")
