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
    r"(?ms)^[ \t]*(?:Fixpoint|CoFixpoint|(?:Local[ \t]+)?Definition|Class|Inductive|Variant"
    r"|(?:#\[[^\]\n]*\][ \t]*)?(?:(?:Global|Local)[ \t]+)?(?:Program[ \t]+)?Instance)\s+"
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


def blank_comments(text: str) -> str:
    """Replace (nested) Rocq comments by spaces, keeping line breaks, so that
    comment prose such as "Notation hint: ..." is never read as a command."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        else:
            out.append(text[i] if not depth or text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def active_context(text: str, stop: int, self_named_instance_context: bool = False,
                   omit_lets: tuple = ()) -> list[str]:
    frames: list[list[str]] = [[]]
    lines = blank_comments(text[:stop]).splitlines()
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
            r"Local\s+Context|Let|Local\s+Definition|Notation|Local\s+Notation|"
            r"#\[local\]\s*Existing\s+Instance)\b",
            stripped,
        ):
            command = [lines[i]]
            while not command[-1].rstrip().endswith("."):
                i += 1
                command.append(lines[i])
            let_name = re.match(rf"^Let\s+({IDENTIFIER_RE})\b", stripped)
            if let_name and let_name.group(1) in omit_lets:
                i += 1
                continue
            frames[-1].extend(command)
        elif m := re.match(rf"^#\[local\]\s*Instance\s+({IDENTIFIER_RE})\b(.*)$", stripped):
            # a source-local instance *definition* (e.g. a section-local readiness
            # model) that later section hypotheses rely on implicitly: in a copied
            # context it becomes a section-local `Let` declared as a local instance,
            # so that it is in scope for the copied hypotheses without being
            # discharged as a (clashing) module-level constant.  The instance itself,
            # when extracted, is a separate byte-identical helper block.
            command = [lines[i]]
            while not command[-1].rstrip().endswith("."):
                i += 1
                command.append(lines[i])
            # An instance whose body names itself re-exposes the imported constant
            # of the same name (e.g. `rs_jlfp_interference := rs_jlfp_interference
            # arr_seq sched`); in the extracted module that name resolves to the
            # extracted helper block instead, so such an instance is not copied
            # (statements name these instances explicitly via printer repairs).
            body = " ".join(command).split(":=", 1)[1] if ":=" in " ".join(command) else ""
            if re.search(rf"(?<![\w.']){re.escape(m.group(1))}(?![\w'])", body):
                if self_named_instance_context:
                    # opt-in (--self-named-instance-context): a later copied context
                    # line (e.g. a section `Let` stated with implicit instances)
                    # relies on this instance, so re-declare it as a section-local
                    # `Let` under a fresh name, registered as a local instance.  Its
                    # body names the extracted helper block of the same name, emitted
                    # earlier in the module, which is definitionally the source instance.
                    indent = lines[i - len(command) + 1][: len(lines[i - len(command) + 1]) - len(stripped)]
                    first = re.sub(rf"#\[local\]\s*Instance\s+{re.escape(m.group(1))}\b",
                                   f"Let {m.group(1)}__source_context", command[0], count=1)
                    frames[-1].extend([first, *command[1:],
                                       f"{indent}#[local] Existing Instance {m.group(1)}__source_context."])
                i += 1
                continue
            indent = lines[i - len(command) + 1][: len(lines[i - len(command) + 1]) - len(stripped)]
            if re.match(r"\s*\{(?!\|)", body):
                # method syntax `{ m := ... }` is only valid in an Instance
                # declaration, not in a `Let`: copy the instance as a
                # context-only local instance under a fresh name (registered
                # for implicit resolution in this copied context only; the
                # extracted helper block keeps its own name and bytes).
                first = re.sub(rf"#\[local\]\s*Instance\s+{re.escape(m.group(1))}\b",
                               f"#[local] Instance {m.group(1)}__source_context", command[0], count=1)
                frames[-1].extend([first, *command[1:]])
                i += 1
                continue
            first = re.sub(r"#\[local\]\s*Instance\s+", "Let ", command[0], count=1)
            frames[-1].extend([first, *command[1:], f"{indent}#[local] Existing Instance {m.group(1)}."])
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
    parser.add_argument(
        "--add-import", action="append", default=[],
        help="validation-only replacement import; recorded in source metadata",
    )
    parser.add_argument(
        "--omit-theorem-context-when-elaborated", action="store_true",
        help=("omit now-unnecessary open Section context around a theorem "
              "whose exact post-Section type comes from elaborated evidence"),
    )
    parser.add_argument(
        "--printer-repair", action="append", default=[],
        help=("OLD=NEW textual repair of a Rocq printing artifact in elaborated "
              "evidence that does not reparse (e.g. '{setTask}={set Task}'); "
              "recorded in metadata.  The generated statement must still print "
              "back to the unrepaired evidence text, which the caller verifies"),
    )
    parser.add_argument(
        "--body-parenthesization", action="append", default=[],
        help=("NAME<TAB>OLD<TAB>NEW: insert parentheses into the body of computational "
              "declaration NAME so that the validation toolchain reproduces the "
              "authoritative parse; OLD must occur exactly once in the block and NEW "
              "may differ from OLD only by added '(' / ')' characters (checked); "
              "recorded in metadata with acquisition mode BODY_PARENTHESIZED"),
    )
    parser.add_argument(
        "--omit-context-let", action="append", default=[],
        help=("NAME of a section `Let` to omit from copied Section contexts; refused when an extracted block "
              "mentions NAME (the Let is then unused by it); recorded in metadata"),
    )
    parser.add_argument(
        "--self-named-instance-context", action="store_true",
        help=("copy a source-local instance that re-exposes the imported constant of the "
              "same name into later copied Section contexts as a context-only local "
              "instance under a fresh name (bound to the earlier extracted helper block); "
              "recorded in metadata"),
    )
    parser.add_argument(
        "--source-order", action="store_true",
        help="emit the requested blocks in source-file order rather than request order "
             "(needed when a helper block depends on a later-requested declaration)",
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
    parenthesizations: dict[str, tuple[str, str]] = {}
    for item in args.body_parenthesization:
        parts = item.split("\t")
        if len(parts) != 3:
            raise SystemExit(f"invalid --body-parenthesization: {item!r}")
        name, old, new = parts
        if re.sub(r"[()]", "", old) != re.sub(r"[()]", "", new) or old == new:
            raise SystemExit(f"--body-parenthesization may only add parentheses: {name}")
        parenthesizations[name] = (old, new)
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
    for name in parenthesizations:
        if name not in computational or declarations[name][1] != "computational":
            raise SystemExit(f"--body-parenthesization needs a requested computational block: {name}")
    for name in type_valued:
        if declarations[name][1] != "theorem":
            raise SystemExit(f"not a theorem declaration: {name}")

    requested_drop_imports = set(args.drop_import)
    command_lines = blank_comments(text).splitlines()
    imports = [
        line for line in command_lines
        if line.strip().startswith(("From ", "Require "))
        and line.strip() not in requested_drop_imports
    ]
    source_imports = {
        line.strip() for line in command_lines
        if line.strip().startswith(("From ", "Require "))
    }
    unknown_drop_imports = requested_drop_imports - source_imports
    if unknown_drop_imports:
        raise SystemExit(
            f"--drop-import commands absent from source: {sorted(unknown_drop_imports)}"
        )
    output = [*imports, *args.add_import, "", f"Module {args.module}.", ""]
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
            "added_validation_imports": args.add_import,
            **({"printer_repairs": args.printer_repair} if args.printer_repair else {}),
            **({"self_named_instance_context": True} if args.self_named_instance_context else {}),
            **({"omitted_context_lets": args.omit_context_let} if args.omit_context_let else {}),
            **({"body_parenthesizations": {n: {"old": o, "new": w} for n, (o, w) in parenthesizations.items()}}
               if parenthesizations else {}),
        },
        "declarations": {},
    }
    if args.source_order:
        requested = sorted(requested, key=lambda name: declarations[name][0])
    for index, name in enumerate(requested):
        position, kind, block = declarations[name]
        # an omitted Let must not be used by the extracted text: the body of a computational block, or the
        # statement of a theorem (proofs are never extracted)
        used_text = block if name in computational else theorem_statement(name, block)
        for let_name in args.omit_context_let:
            if re.search(rf"(?<![\w.']){re.escape(let_name)}(?![\w'])", used_text):
                raise SystemExit(f"--omit-context-let {let_name}: used by extracted block {name}")
        context = active_context(text, position, args.self_named_instance_context,
                                 tuple(args.omit_context_let))
        omitted_context = bool(
            args.omit_theorem_context_when_elaborated
            and elaborated_evidence is not None and kind == "theorem"
        )
        if omitted_context:
            context = []
        # local bindings reconnect Section variables, so they only apply to
        # blocks that are regenerated inside their Section context; a binding
        # that a copied context line (e.g. a hypothesis naming an earlier
        # closed-section definition) mentions is placed just before that line
        context_bindings = {
            binding_name: term for binding_name, term in bindings.items()
            if context and name != binding_name
            and any(re.search(rf"\b{re.escape(binding_name)}\b", line) for line in context)
        }
        if context:
            # regroup the copied lines into whole commands (each ends with '.')
            commands: list[list[str]] = []
            for line in context:
                if not commands or commands[-1][-1].rstrip().endswith("."):
                    commands.append([])
                commands[-1].append(line)
            emitted_context = []
            pending = dict(context_bindings)
            for command in commands:
                for binding_name in list(pending):
                    if any(re.search(rf"\b{re.escape(binding_name)}\b", line) for line in command):
                        emitted_context.append(
                            f"  Local Notation {binding_name} := ({pending.pop(binding_name)}).")
                emitted_context.extend(command)
            output.extend([f"Section SourceContext_{index}.", *emitted_context, ""])
        active_bindings = {
            binding_name: term for binding_name, term in bindings.items()
            if context and name != binding_name and binding_name not in context_bindings
            and re.search(rf"\b{re.escape(binding_name)}\b", block)
        }
        for binding_name, term in active_bindings.items():
            output.append(f"Local Notation {binding_name} := ({term}).")
        if active_bindings:
            output.append("")
        active_bindings = {**context_bindings, **active_bindings}
        if name in computational:
            generated = block.rstrip()
            mode = "BODY_EXACT"
            if name in parenthesizations:
                old, new = parenthesizations[name]
                if generated.count(old) != 1:
                    raise SystemExit(f"--body-parenthesization text must occur once: {name}")
                generated = generated.replace(old, new)
                if re.sub(r"[()]", "", generated) != re.sub(r"[()]", "", block.rstrip()):
                    raise SystemExit(f"--body-parenthesization changed more than parentheses: {name}")
                mode = "BODY_PARENTHESIZED"
            output.extend([generated, ""])
            statement = None
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
                for repair in args.printer_repair:
                    old, new = repair.split("=", 1)
                    elaborated_type = elaborated_type.replace(old, new)
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
            "omitted_context_for_elaborated_theorem": omitted_context,
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
