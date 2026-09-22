#!/usr/bin/env python3
"""Extract proof-independent semantic source signatures from pinned Prosa.

Computational declarations are copied byte-for-byte.  Lemma/theorem blocks
are represented by definitions whose bodies are the exact source statement
text.  They are Prop-valued by default; explicitly listed informative views
(for example MathComp [reflect]) retain their elaborated Type-valued sort.
No proof constant, axiom, or admitted term is generated.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


IDENTIFIER_RE = r"(?:[^\W\d]|_)[\w']*"
IDENTIFIER_BOUNDARY_RE = r"(?![\w'])"

DECL_RE = re.compile(
    r"(?ms)^[ \t]*(?:Lemma|Theorem|Fact|Corollary|Remark|Proposition)\s+"
    rf"({IDENTIFIER_RE}){IDENTIFIER_BOUNDARY_RE}.*?^[^\n]*(?:Qed|Defined)\.[ \t]*$"
)
BODY_RE = re.compile(
    r"(?ms)^[ \t]*(?:Fixpoint|CoFixpoint|Definition)\s+"
    rf"({IDENTIFIER_RE}){IDENTIFIER_BOUNDARY_RE}.*?\.[ \t]*$"
    r"(?:\n(?:[ \t]*\n)*[ \t]*Proof\.[ \t]*$.*?^[^\n]*Defined\.[ \t]*$)?"
)


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_text(text: str) -> str:
    return sha_bytes(text.encode())


def blocks(text: str) -> dict[str, tuple[int, str, str]]:
    found: list[tuple[int, str, str, str]] = []
    for kind, pattern in (("theorem", DECL_RE), ("computational", BODY_RE)):
        for match in pattern.finditer(text):
            found.append((match.start(), match.group(1), kind, match.group(0).lstrip("\n")))
    return {name: (position, kind, block) for position, name, kind, block in sorted(found)}


def active_context(text: str, stop: int) -> list[str]:
    frames: list[list[str]] = [[]]
    lines = text[:stop].splitlines()
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if re.match(rf"^Section\s+{IDENTIFIER_RE}\.$", stripped):
            frames.append([])
        elif re.match(rf"^End(?:\s+{IDENTIFIER_RE})?\.$", stripped):
            if len(frames) > 1:
                frames.pop()
        elif re.match(
            r"^(?:Variable|Variables|Hypothesis|Hypotheses|Context|"
            r"Local\s+Context|Notation|Local\s+Notation)\b",
            stripped,
        ):
            command = [lines[i]]
            while not command[-1].rstrip().endswith("."):
                i += 1
                command.append(lines[i])
            frames[-1].extend(command)
        i += 1
    return [line for frame in frames for line in frame]


def theorem_statement(name: str, block: str) -> str:
    header = re.split(r"(?m)^[ \t]*Proof\.", block, maxsplit=1)[0].strip()
    match = re.match(
        rf"(?s)^(?:Lemma|Theorem|Fact|Corollary|Remark|Proposition)\s+"
        rf"{re.escape(name)}{IDENTIFIER_BOUNDARY_RE}(.*)\.\s*$",
        header,
    )
    if not match:
        raise SystemExit(f"cannot isolate theorem statement: {name}")
    remainder = match.group(1).strip()
    depth = 0
    separator = None
    for index, char in enumerate(remainder):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and depth == 0:
            separator = index
            break
    if separator is None:
        raise SystemExit(f"cannot isolate theorem statement: {name}")
    binders = remainder[:separator].strip()
    conclusion = remainder[separator + 1:].strip()
    return conclusion if not binders else f"forall {binders}, {conclusion}"


def normalized(text: str) -> str:
    return " ".join(text.split())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--source-file", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--declarations", required=True)
    parser.add_argument("--computational", default="")
    parser.add_argument(
        "--type-valued", default="",
        help=("comma-separated theorem declarations whose elaborated statement "
              "lives in Type/Set rather than Prop (for example reflect views)"),
    )
    parser.add_argument(
        "--elaborated-evidence", type=Path,
        help=("optional declaration_type_evidence.json; when present, theorem "
              "statement definitions use the verified post-Section Rocq type"),
    )
    parser.add_argument(
        "--qualified-prefix", default="",
        help="qualified Rocq declaration prefix used with --elaborated-evidence",
    )
    parser.add_argument(
        "--local-binding", action="append", default=[],
        help="NAME=TERM local notation used to reconnect a closed Section declaration",
    )
    parser.add_argument(
        "--drop-import", action="append", default=[],
        help=("exact import command to omit when it is irrelevant to every "
              "extracted declaration; the omission is recorded in metadata"),
    )
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    args = parser.parse_args()

    requested = [name for name in args.declarations.split(",") if name]
    computational = {name for name in args.computational.split(",") if name}
    type_valued = {name for name in args.type_valued.split(",") if name}
    bindings: dict[str, str] = {}
    for item in args.local_binding:
        if "=" not in item:
            raise SystemExit(f"invalid --local-binding: {item}")
        name, term = item.split("=", 1)
        bindings[name] = term
    source = args.source_root / args.source_file
    source_bytes = source.read_bytes()
    text = source_bytes.decode()
    declarations = blocks(text)
    elaborated_evidence = None
    if args.elaborated_evidence is not None:
        if not args.qualified_prefix:
            raise SystemExit("--qualified-prefix is required with --elaborated-evidence")
        elaborated_evidence = json.loads(args.elaborated_evidence.read_text())
    missing = sorted(set(requested) - set(declarations))
    if missing:
        raise SystemExit(f"source declarations not found: {missing}")
    for name in computational:
        if declarations[name][1] != "computational":
            raise SystemExit(f"not a computational declaration: {name}")
    for name in type_valued:
        if declarations[name][1] != "theorem":
            raise SystemExit(f"not a theorem declaration: {name}")

    requested_drop_imports = set(args.drop_import)
    imports = [
        line for line in text.splitlines()
        if line.strip().startswith(("From ", "Require "))
        and line.strip() not in requested_drop_imports
    ]
    source_imports = {
        line.strip() for line in text.splitlines()
        if line.strip().startswith(("From ", "Require "))
    }
    unknown_drop_imports = requested_drop_imports - source_imports
    if unknown_drop_imports:
        raise SystemExit(
            f"--drop-import commands absent from source: {sorted(unknown_drop_imports)}"
        )
    output = [*imports, "", f"Module {args.module}.", ""]
    metadata: dict[str, object] = {
        "mode": "proof_independent_semantic_source_signature",
        "source_file": args.source_file,
        "source_file_sha256": sha_bytes(source_bytes),
        "source_commit": subprocess.check_output(
            ["git", "-C", str(args.source_root), "rev-parse", "HEAD"], text=True
        ).strip(),
        "generated_file": str(args.output),
        "transformations": {
            "computational": "byte-identical declaration block",
            "theorem": (
                "verified post-Section Check type converted to a definition "
                "with its declared Prop/Type sort preserved; exact source header "
                "retained as provenance; opaque proof omitted"
                if elaborated_evidence is not None else
                "exact source statement converted to a definition with its "
                "declared Prop/Type sort preserved; opaque proof omitted"
            ),
            "local_bindings": bindings,
            "dropped_irrelevant_imports": sorted(requested_drop_imports),
        },
        "declarations": {},
    }
    for index, name in enumerate(requested):
        position, kind, block = declarations[name]
        context = active_context(text, position)
        output.extend([f"Section SourceContext_{index}.", *context, ""] if context else [])
        active_bindings = {
            binding_name: term for binding_name, term in bindings.items()
            if name != binding_name and re.search(rf"\b{re.escape(binding_name)}\b", block)
        }
        for binding_name, term in active_bindings.items():
            output.append(f"Local Notation {binding_name} := ({term}).")
        if active_bindings:
            output.append("")
        if name in computational:
            generated = block.rstrip()
            output.extend([generated, ""])
            statement = None
            mode = "BODY_EXACT"
        else:
            statement = theorem_statement(name, block)
            elaborated_type = None
            if elaborated_evidence is not None:
                key = f"{args.qualified_prefix}.{name}"
                evidence = elaborated_evidence.get(key)
                if evidence is None:
                    raise SystemExit(f"missing elaborated type evidence: {key}")
                check = evidence.get("normalized_check")
                if not check or ":" not in check:
                    raise SystemExit(f"malformed elaborated type evidence: {key}")
                elaborated_type = check.split(":", 1)[1].strip()
                statement_sort = "Type" if name in type_valued else "Prop"
                generated = (
                    f"Definition statement_{name} : {statement_sort} :=\n"
                    f"  ({elaborated_type})."
                )
            else:
                statement_sort = "Type" if name in type_valued else "Prop"
                generated = (
                    f"Definition statement_{name} : {statement_sort} :=\n"
                    f"  ({statement})."
                )
            output.extend([generated, ""])
            mode = "STATEMENT_EXACT_PROOF_OMITTED"
        if context:
            output.extend([f"End SourceContext_{index}.", ""])
        metadata["declarations"][name] = {
            "source_kind": kind,
            "acquisition_mode": mode,
            "source_block_sha256": sha_text(block),
            "generated_text_sha256": sha_text(generated),
            "source_statement_sha256": None if statement is None else sha_text(statement),
            "normalized_statement_sha256": None if statement is None else sha_text(normalized(statement)),
            "elaborated_type_sha256": (
                None if kind == "computational" or elaborated_evidence is None
                else sha_text(elaborated_type)
            ),
            "elaborated_type_evidence": (
                None if kind == "computational" or elaborated_evidence is None
                else "ELABORATED_ROCQ_CHECK"
            ),
            "statement_sort": (
                None if kind == "computational"
                else ("Type" if name in type_valued else "Prop")
            ),
            "context": context,
            "local_bindings": active_bindings,
        }
    output.extend([f"End {args.module}.", ""])

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(output))
    args.metadata.write_text(json.dumps(metadata, indent=2) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
