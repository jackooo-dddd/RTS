#!/usr/bin/env python3
"""Generate declaration-method and foundational-chain audit documents."""

from __future__ import annotations

import argparse
import csv
import json
import re
from collections import Counter
from pathlib import Path

from generate_v06_inventory import command_end, module_of, parse_declarations, parse_glob, strip_comments


FOUNDATIONS = [
    "prosa.behavior.job.JobType",
    "prosa.behavior.job.JobArrival",
    "prosa.behavior.job.JobCost",
    "prosa.behavior.schedule.ProcessorState",
    "prosa.behavior.schedule.scheduled_in",
    "prosa.behavior.schedule.supply_in",
    "prosa.behavior.schedule.service_in",
    "prosa.behavior.service.service_at",
    "prosa.behavior.service.service_during",
    "prosa.behavior.service.service",
    "prosa.behavior.service.completed_by",
    "prosa.behavior.service.completes_at",
    "prosa.model.task.concept.TaskType",
    "prosa.model.task.concept.JobTask",
]


def defined_audit(source: Path) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    header_re = re.compile(
        r"(?m)^[ \t]*(?P<attrs>(?:#\[[^]]+\]\s*)*)(?:(?:Local|Global)\s+)?"
        r"(?:Program\s+)?(?P<kind>Definition|Fixpoint|CoFixpoint|Instance)\b"
        r"(?:\s+(?P<name>[^\W\d][\w']*))?"
    )
    for path in sorted(source.rglob("*.v")):
        if ".git" in path.parts:
            continue
        raw = path.read_text(errors="replace")
        clean = strip_comments(raw)
        headers = list(header_re.finditer(clean))
        refs, _ = parse_glob(path.with_suffix(".glob"))
        for terminator in re.finditer(r"(?m)^[ \t]*Defined\s*\.", clean):
            candidates = [header for header in headers if header.start() < terminator.start()]
            if not candidates:
                continue
            header = candidates[-1]
            header_end_char = command_end(clean, header.start())
            if header_end_char > terminator.start():
                continue
            between = clean[header_end_char:terminator.start()]
            if "Qed." in between or "Defined." in between or "Abort." in between:
                continue
            body_start = len(raw[:header_end_char].encode())
            body_end = len(raw[:terminator.end()].encode())
            body_refs = [ref["qualified"] for ref in refs if body_start <= ref["start"] < body_end]
            attrs = header.group("attrs") or ""
            result.append({
                "source_file": path.relative_to(source).as_posix(),
                "line": clean.count("\n", 0, header.start()) + 1,
                "kind": header.group("kind"), "name": header.group("name") or "<anonymous>",
                "attributes": attrs.strip(), "body_reference_count": len(body_refs),
                "body_references": sorted(set(body_refs)),
                "public_named_inventory_node": bool(header.group("name")) and "local" not in attrs,
            })
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    source, out = args.source.resolve(), args.output.resolve()
    inventory = list(csv.DictReader((out / "declaration_inventory.csv").open()))
    layers = {row["qualified_name"]: row for row in csv.DictReader((out / "declaration_layers.csv").open())}
    edges = list(csv.DictReader((out / "declaration_dag_edges.csv").open()))
    evidence = json.loads((out / "declaration_type_evidence.json").read_text())
    dag = json.loads((out / "declaration_dag.json").read_text())
    summary = json.loads((out / "generation_summary.json").read_text())
    declarations = {row["qualified_name"]: row for row in inventory}

    source_commands: dict[str, str] = {}
    for path in sorted(source.rglob("*.v")):
        if ".git" in path.parts:
            continue
        relative = path.relative_to(source).as_posix()
        raw = path.read_text(errors="replace")
        for declaration in parse_declarations(path, module_of(relative)):
            source_commands[declaration["qualified_name"]] = raw[declaration["start_char"]:declaration["end_char"]].strip()

    defined = defined_audit(source)
    dag["defined_body_audit"] = defined
    (out / "declaration_dag.json").write_text(json.dumps(dag, indent=2, sort_keys=True) + "\n")

    edge_evidence = Counter(
        category for edge in edges for category in edge["evidence_categories"].split(";") if category
    )
    mapping_methods = Counter(item["mapping_method"] for item in dag["generated_symbol_mappings"])
    unresolved_kinds = Counter(item["symbol_kind"] for item in dag["unresolved_generated_symbols"])
    confidence = Counter(row["dependency_extraction_confidence"] for row in layers.values())

    method = [
        "# Declaration Dependency Extraction Method", "",
        "## Status", "",
        "```text",
        "FILE_DAG_STATUS = VERIFIED_COMPLETE_FOR_PINNED_SOURCE",
        "DECLARATION_DAG_STATUS =",
        "VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES",
        "WITH_DOCUMENTED_IMPLICIT/GENERATED LIMITATIONS",
        "```", "",
        "The file graph remains the authoritative translation-readiness graph. The declaration graph is a fine-grained scheduling and context aid; it must not be used as the sole criterion that a declaration's environment is ready.", "",
        "## Evidence classes", "",
        "- `EXPLICIT_GLOB_DEPENDENCY`: a Rocq `.glob` reference location lies inside the source declaration's final type command or included computational body span.",
        "- `ELABORATED_TYPE_CONFIRMED`: the dependent declaration's actual post-Section-closure type was resolved and printed by Rocq `Check @qualified.name`. This confirms the final type, not that every dependency edge was recovered.",
        "- `GENERATED_SYMBOL_MAPPED`: a reference to a constructor/projection/HB-generated symbol was mapped to a public source owner without adding the generated symbol to the public inventory.",
        "- `UNRESOLVED_IMPLICIT_DEPENDENCY`: `.glob` does not provide a completeness theorem for implicit typeclass search, canonical structures, or HB resolution. No missing edge is guessed.", "",
        "## Actual extraction totals", "",
        f"- Public source declarations: **{len(inventory)}**.",
        f"- Direct declaration edges: **{len(edges)}**.",
        f"- Generated-symbol mappings: **{len(dag['generated_symbol_mappings'])}**.",
        f"- Edges using a generated-symbol mapping: **{summary['generated_symbol_edges']}**.",
        f"- Generated/local symbols referenced but not unambiguously mapped: **{len(dag['unresolved_generated_symbols'])}**.",
        f"- Confidence distribution: `{dict(confidence)}`.",
        f"- Edge evidence occurrences: `{dict(edge_evidence)}`.",
        f"- Mapping methods: `{dict(mapping_methods)}`.",
        f"- Unresolved generated/local kinds: `{dict(unresolved_kinds)}`.", "",
        "## Generated symbols", "",
        "Constructors and projections are mapped by a byte-accurate source span shared with their owner `Inductive`, `Record`, `Structure`, or `Class`. HB symbols are mapped only when the same `HB.instance Definition _` command explicitly references exactly one public structural owner. Ambiguous cases remain unresolved. Compiler-generated symbols never become public inventory nodes.", "",
        "## `Definition ... Proof ... Defined` audit", "",
        f"The pinned tree contains **{len(defined)}** computational declaration(s) ending in `Defined.`.",
    ]
    if defined:
        method += ["", "| File | Line | Kind | Name | Public named node | Body refs |", "|---|---:|---|---|---|---:|"]
        for item in defined:
            method.append(f"| `{item['source_file']}` | {item['line']} | {item['kind']} | `{item['name']}` | {item['public_named_inventory_node']} | {item['body_reference_count']} |")
    method += ["",
        "At v0.6 the sole occurrence is the anonymous global `RewriteRelation le` instance in `util/setoid.v`. It has no proof-body references between its header and `Defined.` and is not a named public declaration node. Therefore the previous named-public DAG missed no computational body edge from this pattern. Its possible participation in later instance search remains covered by `UNRESOLVED_IMPLICIT_DEPENDENCY`.", "",
        "For a named `Definition`/`Fixpoint`/`CoFixpoint`/`Instance` ending in `Defined.`, the extractor now extends the body span through `Defined.`. Opaque `Qed.` proof bodies and all theorem/lemma proof bodies remain excluded.", "",
        "## Implicit resolution limitation", "",
        "Spot inspection shows that `.glob` records many selected `inst` references and all source-located projection/constructor references, but it does not establish that every elaborator-inserted typeclass, canonical-structure, coercion, or HB dependency has a recoverable source location. In particular, 71 referenced local/generated symbols have no unambiguous public owner (mostly local proof constants and local instances). The graph records them but does not invent edges.", "",
        "## Scheduling rule", "",
        "Use `file_layers.csv` as the mandatory readiness order. Use `declaration_layers.csv` only to order work within an already-ready file/dependency context. Absence of a declaration edge is not evidence of semantic independence.", "",
    ]
    (out / "declaration_dependency_method.md").write_text("\n".join(method))

    audit = ["# Foundational Declaration Dependency Audit", "",
             "Pinned source: Prosa v0.6 commit `414e66760333eaa4ef78c685bcf53291c527a548`.", "",
             "Every entry below uses the elaborated Rocq type captured by `Check`, the official source command, and direct edges from the hardened graph. `UNRESOLVED_IMPLICIT_DEPENDENCY` means the explicit edge list is not claimed exhaustive.", ""]
    for name in FOUNDATIONS:
        declaration = declarations[name]
        layer = layers[name]
        direct = sorted((edge for edge in edges if edge["dependent"] == name), key=lambda x: (x["dependency"], x["edge_type"]))
        mapped = [edge for edge in direct if "GENERATED_SYMBOL_MAPPED" in edge["evidence_categories"]]
        audit += [f"## `{name}`", "",
                  f"- Source: `{declaration['source_file']}:{declaration['source_line']}`; kind: `{declaration['kind']}`.",
                  f"- Declaration layer: {layer['layer']}; confidence: `{layer['dependency_extraction_confidence']}`.",
                  f"- Implicit/canonical/HB risk: `{layer['implicit_dependency_status']}`.",
                  f"- Direct internal dependencies: {len(direct)}; generated-symbol-mapped edges: {len(mapped)}.", "",
                  "Elaborated Rocq type:", "", "```text", evidence[name]["rendered_check"], "```", "",
                  "Official source declaration/body:", "", "```coq", source_commands[name], "```", ""]
        if direct:
            audit += ["Direct extracted dependencies:", "", "| Dependency | Edge kind | Region | Evidence | Generated symbol / mapping |", "|---|---|---|---|---|"]
            for edge in direct:
                generated = edge["generated_symbols"]
                if edge["mapping_methods"]:
                    generated += " / " + edge["mapping_methods"]
                audit.append(f"| `{edge['dependency']}` | {edge['edge_type']} | {edge['reference_region']} | {edge['evidence_categories']} | {generated} |")
            audit.append("")
        else:
            audit += ["Direct extracted dependencies: none. This means no explicit/mapped internal edge was recovered; it does **not** prove independence from implicit resolution.", ""]
    (out / "foundation_dependency_audit.md").write_text("\n".join(audit))


if __name__ == "__main__":
    main()
