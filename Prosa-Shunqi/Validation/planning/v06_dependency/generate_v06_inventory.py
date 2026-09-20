#!/usr/bin/env python3
"""Generate the pinned Prosa v0.6 source and dependency inventory.

File edges come from coqdep.  Source parsing is used to retain Require
Import/Export distinctions and external boundaries.  Declaration edges come
from Rocq .glob references restricted to each source declaration's statement
or computational body; proof-body references are deliberately excluded.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any, Iterable


PINNED_COMMIT = "414e66760333eaa4ef78c685bcf53291c527a548"
DECL_KINDS = (
    "Definition", "Fixpoint", "CoFixpoint", "Inductive", "Variant",
    "CoInductive", "Record", "Structure", "Class", "Instance", "Lemma",
    "Theorem", "Corollary", "Fact", "Remark", "Proposition", "Example",
)
THEOREM_KINDS = {"Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition", "Example"}
STRUCTURE_KINDS = {"Record", "Structure", "Class"}
DECL_RE = re.compile(
    r"(?m)^[ \t]*(?P<attributes>(?:#\[[^\]]+\]\s*)*)"
    r"(?P<scope>Local\s+|Global\s+)?(?P<program>Program\s+)?"
    r"(?P<kind>" + "|".join(DECL_KINDS) + r")\s+(?P<name>[^\W\d][\w']*)"
)
REQUIRE_RE = re.compile(
    r"(?ms)^[ \t]*(?:From\s+(?P<root>[A-Za-z0-9_.]+)\s+)?Require\s+"
    r"(?:(?P<mode>Import|Export)\s+)?(?P<modules>.*?)\.(?=\s|$)"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(command: list[str], cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {' '.join(command)}\n{result.stderr}")
    return result


def strip_comments(text: str) -> str:
    """Blank nested Rocq comments while preserving offsets and newlines."""
    out = list(text)
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        else:
            if depth and text[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def command_end(text: str, start: int) -> int:
    """Find a vernacular command terminator, preserving source offsets."""
    paren = bracket = brace = 0
    in_string = False
    i = start
    while i < len(text):
        ch = text[i]
        if ch == '"':
            if in_string and i + 1 < len(text) and text[i + 1] == '"':
                i += 2
                continue
            in_string = not in_string
        elif not in_string:
            if ch == "(": paren += 1
            elif ch == ")": paren = max(0, paren - 1)
            elif ch == "[": bracket += 1
            elif ch == "]": bracket = max(0, bracket - 1)
            elif ch == "{": brace += 1
            elif ch == "}": brace = max(0, brace - 1)
            elif ch == "." and paren == bracket == brace == 0:
                nxt = text[i + 1:i + 2]
                if not nxt or nxt.isspace():
                    return i + 1
        i += 1
    return len(text)


def top_level_assignment(text: str, start: int, end: int) -> int | None:
    paren = bracket = brace = 0
    in_string = False
    i = start
    while i + 1 < end:
        ch = text[i]
        if ch == '"': in_string = not in_string
        elif not in_string:
            if ch == "(": paren += 1
            elif ch == ")": paren = max(0, paren - 1)
            elif ch == "[": bracket += 1
            elif ch == "]": bracket = max(0, bracket - 1)
            elif ch == "{": brace += 1
            elif ch == "}": brace = max(0, brace - 1)
            elif text.startswith(":=", i) and paren == bracket == brace == 0:
                return i
        i += 1
    return None


def module_of(path: str) -> str:
    return "prosa." + path[:-2].replace("/", ".")


def classify_file(path: str) -> tuple[str, str, str]:
    if path.startswith("implementation/refinements/"):
        return "IMPLEMENTATION_REFINEMENT", "refinements", "requires rocq-prosa plus external CoqEAL"
    if path.startswith("implementation/"):
        return "IMPLEMENTATION", "main", "executable/constructive implementation within the main package"
    name = Path(path).stem.lower()
    if name in {"example", "examples", "test", "tests"}:
        return "LIBRARY_EXAMPLE", "main", "example module shipped and built as part of the library"
    if name == "all":
        return "CORE_AGGREGATOR", "main", "public re-export/aggregation module"
    return "CORE_PROSA", "main", "core specification, model, analysis, result, or utility module"


def parse_requires(text: str) -> list[dict[str, str]]:
    clean = strip_comments(text)
    rows: list[dict[str, str]] = []
    for match in REQUIRE_RE.finditer(clean):
        root = match.group("root") or ""
        mode = match.group("mode") or "PLAIN_REQUIRE"
        tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", match.group("modules"))
        for token in tokens:
            full = f"{root}.{token}" if root else token
            rows.append({"module": full, "edge_type": "REQUIRE_EXPORT" if mode == "Export" else "REQUIRE_IMPORT"})
    return rows


def parse_coqdep(text: str, known: dict[str, str]) -> set[tuple[str, str]]:
    logical_lines: list[str] = []
    pending = ""
    for line in text.splitlines():
        pending += line.rstrip("\\") + (" " if line.endswith("\\") else "")
        if not line.endswith("\\"):
            logical_lines.append(pending)
            pending = ""
    edges: set[tuple[str, str]] = set()
    for line in logical_lines:
        if ":" not in line:
            continue
        lhs, rhs = line.split(":", 1)
        target_match = re.search(r"(?:^|\s)(\./[^ ]+)\.vo(?=\s|$)", lhs)
        if not target_match:
            continue
        target = target_match.group(1)[2:] + ".v"
        if target not in known:
            continue
        for dep in re.findall(r"(?:^|\s)(\./[^ ]+)\.vo(?=\s|$)", rhs):
            source = dep[2:] + ".v"
            if source in known and source != target:
                edges.add((source, target))
    return edges


def tarjan(nodes: Iterable[str], edges: Iterable[tuple[str, str]]) -> list[list[str]]:
    adjacency: dict[str, list[str]] = defaultdict(list)
    for a, b in sorted(edges): adjacency[a].append(b)
    index = 0
    indices: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    result: list[list[str]] = []

    def visit(v: str) -> None:
        nonlocal index
        indices[v] = low[v] = index; index += 1
        stack.append(v); on_stack.add(v)
        for w in adjacency[v]:
            if w not in indices:
                visit(w); low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], indices[w])
        if low[v] == indices[v]:
            component = []
            while True:
                w = stack.pop(); on_stack.remove(w); component.append(w)
                if w == v: break
            result.append(sorted(component))
    for node in sorted(nodes):
        if node not in indices: visit(node)
    return result


def graph_metrics(nodes: list[str], edges: set[tuple[str, str]]) -> dict[str, Any]:
    components = tarjan(nodes, edges)
    comp_of = {node: i for i, comp in enumerate(components) for node in comp}
    c_edges = {(comp_of[a], comp_of[b]) for a, b in edges if comp_of[a] != comp_of[b]}
    pred: dict[int, set[int]] = defaultdict(set)
    succ: dict[int, set[int]] = defaultdict(set)
    for a, b in sorted(c_edges): succ[a].add(b); pred[b].add(a)
    indegree = {i: len(pred[i]) for i in range(len(components))}
    queue = deque(sorted(i for i, degree in indegree.items() if degree == 0))
    order: list[int] = []
    layers = {i: 0 for i in queue}
    while queue:
        current = queue.popleft(); order.append(current)
        for nxt in sorted(succ[current]):
            layers[nxt] = max(layers.get(nxt, 0), layers[current] + 1)
            indegree[nxt] -= 1
            if indegree[nxt] == 0: queue.append(nxt)
    node_layer = {node: layers[comp_of[node]] for node in nodes}
    longest_to: dict[int, list[int]] = {}
    for component in order:
        candidates = [longest_to[p] for p in pred[component]]
        longest_to[component] = (max(candidates, key=len) if candidates else []) + [component]
    longest_components = max(longest_to.values(), key=len) if longest_to else []
    longest_chain = [components[component][0] for component in longest_components]

    adjacency: dict[str, set[str]] = defaultdict(set)
    reverse: dict[str, set[str]] = defaultdict(set)
    for a, b in sorted(edges): adjacency[a].add(b); reverse[b].add(a)
    def reachable(start: str, graph: dict[str, set[str]]) -> set[str]:
        seen: set[str] = set(); todo = list(graph[start])
        while todo:
            item = todo.pop()
            if item not in seen:
                seen.add(item); todo.extend(graph[item] - seen)
        return seen
    return {
        "components": components, "component_edges": sorted(c_edges), "component_order": order,
        "longest_chain": longest_chain,
        "cycles": [comp for comp in components if len(comp) > 1], "layer": node_layer,
        "dependents": {n: adjacency[n] for n in nodes}, "dependencies": {n: reverse[n] for n in nodes},
        "transitive_dependents": {n: reachable(n, adjacency) for n in nodes},
        "transitive_dependencies": {n: reachable(n, reverse) for n in nodes},
    }


def parse_declarations(path: Path, module: str) -> list[dict[str, Any]]:
    raw = path.read_text(errors="replace")
    clean = strip_comments(raw)
    declarations: list[dict[str, Any]] = []
    order = 0
    for match in DECL_RE.finditer(clean):
        attributes = match.group("attributes") or ""
        if (match.group("scope") or "").strip() == "Local" or re.search(r"#\[[^]]*\blocal\b", attributes):
            continue
        kind, name = match.group("kind"), match.group("name")
        header_end = command_end(clean, match.start())
        assignment = top_level_assignment(clean, match.start(), header_end)
        extraction_end = header_end
        computational_body_mode = "INLINE_BODY" if assignment is not None else "NO_INLINE_BODY"
        if kind in {"Definition", "Fixpoint", "CoFixpoint", "Instance"} and assignment is None:
            tail = clean[header_end:]
            proof = re.match(r"\s*Proof\s*\.", tail)
            if proof:
                terminator = re.search(r"(?m)^[ \t]*(Defined|Qed|Admitted|Abort)\s*\.", tail[proof.end():])
                if terminator:
                    mode = terminator.group(1)
                    if mode == "Defined":
                        extraction_end = header_end + proof.end() + terminator.end()
                        computational_body_mode = "PROOF_DEFINED_BODY_INCLUDED"
                    else:
                        computational_body_mode = f"OPAQUE_PROOF_{mode.upper()}_EXCLUDED"
        fields: list[dict[str, str]] = []
        if kind in STRUCTURE_KINDS:
            block = clean[match.end():header_end]
            for field in re.finditer(r"(?m)(?:^|[{;])[ \t]*([^\W\d][\w']*)\s*(?:[^:\n]*?)\s*:\s*([^;\n}]+)", block):
                fields.append({"name": field.group(1), "source_type": " ".join(field.group(2).split())})
            if not fields and assignment is not None:
                single = re.match(r"\s*([^\W\d][\w']*)\s*:\s*(.*)\.\s*$",
                                  clean[assignment + 2:header_end], re.S)
                if single:
                    fields.append({"name": single.group(1), "source_type": " ".join(single.group(2).split())})
        order += 1
        start_byte = len(raw[:match.start()].encode())
        header_end_byte = len(raw[:header_end].encode())
        extraction_end_byte = len(raw[:extraction_end].encode())
        assignment_byte = len(raw[:assignment].encode()) if assignment is not None else None
        declarations.append({
            "source_file": path.name, "module": module, "declaration_name": name,
            "qualified_name": f"{module}.{name}", "kind": kind, "source_order": order,
            "source_line": clean.count("\n", 0, match.start()) + 1,
            "start": start_byte, "end": extraction_end_byte, "header_end": header_end_byte,
            "assignment": assignment_byte, "start_char": match.start(),
            "end_char": extraction_end, "header_end_char": header_end,
            "statement_end": header_end_byte, "structure_fields": fields,
            "attributes": attributes.strip(), "computational_body_mode": computational_body_mode,
            "source_command_sha256": sha256_bytes(raw[match.start():extraction_end].encode()),
        })
    return declarations


def parse_glob(path: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    refs: list[dict[str, Any]] = []
    symbols: list[dict[str, Any]] = []
    if not path.exists(): return refs, symbols
    module = ""
    for line in path.read_text(errors="replace").splitlines():
        if line.startswith("F"):
            module = line[1:]
            continue
        declaration = re.match(r"(ind|constr|rec|proj|def|prf|thm|inst|class)\s+(\d+):(\d+)\s+\S+\s+(\S+)", line)
        if declaration and module:
            kind, start, end, name = declaration.groups()
            symbols.append({"start": int(start), "end": int(end) + 1,
                            "qualified": f"{module}.{name}", "name": name, "kind": kind})
            continue
        match = re.match(r"R(\d+):(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)", line)
        if not match: continue
        start, end, library, namespace, name, kind = match.groups()
        if ":" in name or kind in {"var", "not"}: continue
        qualified = f"{library}.{name}"
        refs.append({"start": int(start), "end": int(end) + 1, "qualified": qualified, "kind": kind})
    return refs, symbols


def csv_write(path: Path, fieldnames: list[str], rows: Iterable[dict[str, Any]]) -> None:
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, extrasaction="ignore", lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--coqdep-output", required=True, type=Path)
    parser.add_argument("--coqdep-errors", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--opam-switch", default="prosa-0.6")
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    commit = run(["git", "-C", str(source), "rev-parse", "HEAD"]).stdout.strip()
    if commit != PINNED_COMMIT: raise SystemExit(f"wrong source commit: {commit}")
    source_tree = run(["git", "-C", str(source), "rev-parse", "HEAD^{tree}"]).stdout.strip()
    paths = sorted(p.relative_to(source).as_posix() for p in source.rglob("*.v") if ".git" not in p.parts)
    module_to_file = {module_of(path): path for path in paths}
    file_to_module = {path: module_of(path) for path in paths}
    def resolve_internal_module(name: str) -> str | None:
        return module_to_file.get(name) or module_to_file.get("prosa." + name)

    parsed_requires: dict[str, list[dict[str, str]]] = {}
    inventory: list[dict[str, Any]] = []
    for relative in paths:
        path = source / relative
        category, build_group, reason = classify_file(relative)
        requires = parse_requires(path.read_text(errors="replace"))
        parsed_requires[relative] = requires
        internal = [r for r in requires if resolve_internal_module(r["module"])]
        external = [r for r in requires if not resolve_internal_module(r["module"])]
        inventory.append({
            "file": relative, "module": file_to_module[relative], "category": category,
            "build_group": build_group, "classification_reason": reason,
            "sha256": sha256_bytes(path.read_bytes()),
            "lines": len(path.read_text(errors="replace").splitlines()),
            "direct_internal_import_count": len(internal),
            "direct_external_import_count": len(external),
        })

    coqdep_edges = parse_coqdep(args.coqdep_output.read_text(errors="replace"), file_to_module)
    source_edge_types: dict[tuple[str, str], set[str]] = defaultdict(set)
    external_rows: list[dict[str, Any]] = []
    unresolved_internal: list[dict[str, str]] = []
    for dependent, requires in parsed_requires.items():
        for req in requires:
            dependency = resolve_internal_module(req["module"])
            if dependency:
                source_edge_types[(dependency, dependent)].add(req["edge_type"])
            else:
                root = req["module"].split(".", 1)[0]
                classification = "PROSA_MODULE_NOT_IN_SOURCE" if root == "prosa" else "EXTERNAL_LIBRARY"
                row = {"dependent_file": dependent, "dependent_module": file_to_module[dependent],
                       "external_module": req["module"], "edge_type": req["edge_type"],
                       "classification": classification}
                external_rows.append(row)
                if classification == "PROSA_MODULE_NOT_IN_SOURCE": unresolved_internal.append(row)
    file_edges = []
    for edge in sorted(coqdep_edges | set(source_edge_types)):
        types = sorted(source_edge_types.get(edge, {"COQDEP_UNTYPED"}))
        file_edges.append({"dependency_file": edge[0], "dependent_file": edge[1],
                           "dependency_module": file_to_module[edge[0]],
                           "dependent_module": file_to_module[edge[1]],
                           "edge_types": ";".join(types),
                           "verified_by_coqdep": edge in coqdep_edges})
    graph_edges = {(r["dependency_file"], r["dependent_file"]) for r in file_edges}
    file_metrics = graph_metrics(paths, graph_edges)
    inventory_by_file = {row["file"]: row for row in inventory}
    layer_rows = []
    for path in paths:
        dependencies = file_metrics["dependencies"][path]
        dependents = file_metrics["dependents"][path]
        external = [r["external_module"] for r in external_rows if r["dependent_file"] == path]
        layer_rows.append({
            "file": path, "module": file_to_module[path], "layer": file_metrics["layer"][path],
            "direct_internal_dependencies": ";".join(sorted(dependencies)),
            "direct_external_dependencies": ";".join(sorted(set(external))),
            "transitive_internal_dependency_count": len(file_metrics["transitive_dependencies"][path]),
            "direct_dependents": ";".join(sorted(dependents)),
            "transitive_dependent_count": len(file_metrics["transitive_dependents"][path]),
        })
        inventory_by_file[path]["layer"] = file_metrics["layer"][path]

    declarations: list[dict[str, Any]] = []
    for relative in paths:
        ds = parse_declarations(source / relative, file_to_module[relative])
        for d in ds: d["source_file"] = relative
        declarations.extend(ds)
    decl_by_qname = {d["qualified_name"]: d for d in declarations}
    declarations_by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for declaration in declarations:
        declarations_by_file[declaration["source_file"]].append(declaration)

    glob_refs: dict[str, list[dict[str, Any]]] = {}
    glob_symbols: dict[str, list[dict[str, Any]]] = {}
    all_glob_symbols: dict[str, dict[str, Any]] = {}
    unresolved_decl_files: list[str] = []
    for relative in paths:
        glob = source / relative[:-2]
        glob = glob.with_suffix(".glob")
        refs, symbols = parse_glob(glob)
        glob_refs[relative], glob_symbols[relative] = refs, symbols
        for symbol in symbols:
            all_glob_symbols[symbol["qualified"]] = {**symbol, "source_file": relative}
        if not glob.exists():
            unresolved_decl_files.append(relative)

    # Generated symbols are not public inventory nodes. Constructors and
    # projections are mapped to the source declaration whose command span
    # caused Rocq to generate them. Relevant HB-generated symbols are mapped
    # only when the same HB command explicitly references exactly one source
    # structural owner; otherwise no edge is guessed.
    generated_mappings: dict[str, dict[str, Any]] = {}
    structural_kinds = STRUCTURE_KINDS | {"Inductive", "Variant", "CoInductive"}
    for relative in paths:
        for declaration in declarations_by_file[relative]:
            if declaration["kind"] not in structural_kinds:
                continue
            for symbol in glob_symbols[relative]:
                if declaration["start"] <= symbol["start"] < declaration["header_end"] \
                        and symbol["qualified"] != declaration["qualified_name"]:
                    generated_mappings[symbol["qualified"]] = {
                        "generated_symbol": symbol["qualified"], "owner": declaration["qualified_name"],
                        "symbol_kind": symbol["kind"], "mapping_method": "SOURCE_DECLARATION_SPAN",
                        "source_file": relative,
                    }
        raw = (source / relative).read_text(errors="replace")
        clean = strip_comments(raw)
        for hb in re.finditer(r"(?m)^[ \t]*HB\.instance\s+Definition\s+_\b", clean):
            hb_end_char = command_end(clean, hb.start())
            hb_start = len(raw[:hb.start()].encode())
            hb_end = len(raw[:hb_end_char].encode())
            candidates = {
                ref["qualified"] for ref in glob_refs[relative]
                if hb_start <= ref["start"] < hb_end
                and ref["qualified"] in decl_by_qname
                and decl_by_qname[ref["qualified"]]["kind"] in structural_kinds
            }
            if len(candidates) != 1:
                continue
            owner = next(iter(candidates))
            for symbol in glob_symbols[relative]:
                if hb_start <= symbol["start"] < hb_end and symbol["qualified"] not in decl_by_qname:
                    generated_mappings[symbol["qualified"]] = {
                        "generated_symbol": symbol["qualified"], "owner": owner,
                        "symbol_kind": symbol["kind"],
                        "mapping_method": "HB_SAME_COMMAND_UNIQUE_STRUCTURAL_OWNER",
                        "source_file": relative,
                    }

    decl_edges_work: dict[tuple[str, str, str], dict[str, Any]] = {}
    generated_use_count: Counter[str] = Counter()
    for relative in paths:
        refs = glob_refs[relative]
        for declaration in declarations_by_file[relative]:
            for ref in refs:
                if not (declaration["start"] <= ref["start"] < declaration["end"]): continue
                target = ref["qualified"]
                mapping = generated_mappings.get(target)
                dependency = target if target in decl_by_qname else mapping["owner"] if mapping else None
                if not dependency or dependency == declaration["qualified_name"]: continue
                body_reference = declaration["kind"] not in structural_kinds and ((
                    declaration["assignment"] is not None and ref["start"] > declaration["assignment"]
                ) or (
                    declaration["computational_body_mode"] == "PROOF_DEFINED_BODY_INCLUDED"
                    and ref["start"] >= declaration["header_end"]
                ))
                if declaration["kind"] in STRUCTURE_KINDS:
                    edge_type = "STRUCTURE_FIELD_DEPENDENCY"
                elif declaration["kind"] == "Instance" or decl_by_qname[dependency]["kind"] == "Instance" or ref["kind"] in {"inst"}:
                    edge_type = "INSTANCE_DEPENDENCY"
                elif declaration["kind"] in THEOREM_KINDS:
                    edge_type = "TYPE_DEPENDENCY"
                elif body_reference:
                    edge_type = "BODY_DEPENDENCY"
                else:
                    edge_type = "TYPE_DEPENDENCY"
                key = (dependency, declaration["qualified_name"], edge_type)
                row = decl_edges_work.setdefault(key, {
                    "dependency": dependency, "dependent": declaration["qualified_name"],
                    "edge_type": edge_type, "source_file": relative,
                    "reference_region": "BODY" if body_reference else "TYPE_OR_STRUCTURE",
                    "evidence_categories": set(), "generated_symbols": set(), "mapping_methods": set(),
                })
                if mapping:
                    row["evidence_categories"].add("GENERATED_SYMBOL_MAPPED")
                    row["generated_symbols"].add(target)
                    row["mapping_methods"].add(mapping["mapping_method"])
                    generated_use_count[target] += 1
                else:
                    row["evidence_categories"].add("EXPLICIT_GLOB_DEPENDENCY")

    decl_edges: dict[tuple[str, str, str], dict[str, Any]] = {}
    for key, row in decl_edges_work.items():
        decl_edges[key] = {
            **{k: v for k, v in row.items() if k not in {"evidence_categories", "generated_symbols", "mapping_methods"}},
            "evidence_categories": ";".join(sorted(row["evidence_categories"])),
            "generated_symbols": ";".join(sorted(row["generated_symbols"])),
            "mapping_methods": ";".join(sorted(row["mapping_methods"])),
            "implicit_dependency_status": "UNRESOLVED_IMPLICIT_DEPENDENCY",
        }

    referenced_internal_symbols = {
        ref["qualified"] for refs in glob_refs.values() for ref in refs
        if ref["qualified"].startswith("prosa.")
    }
    unresolved_generated_symbols = []
    for symbol in sorted(referenced_internal_symbols & set(all_glob_symbols)):
        if symbol in decl_by_qname or symbol in generated_mappings:
            continue
        item = all_glob_symbols[symbol]
        unresolved_generated_symbols.append({
            "symbol": symbol, "symbol_kind": item["kind"], "source_file": item["source_file"],
            "status": "UNRESOLVED_IMPLICIT_DEPENDENCY",
            "reason": "internal generated/local symbol has no unambiguous public source owner",
        })
    decl_nodes = sorted(decl_by_qname)
    decl_graph_edges = {(a, b) for a, b, _ in decl_edges}
    decl_metrics = graph_metrics(decl_nodes, decl_graph_edges)
    dependents_with_generated_mapping = {
        row["dependent"] for row in decl_edges.values()
        if "GENERATED_SYMBOL_MAPPED" in row["evidence_categories"]
    }
    decl_layer_rows = []
    for name in decl_nodes:
        d = decl_by_qname[name]
        if d["source_file"] in unresolved_decl_files:
            confidence = "UNRESOLVED_EXTERNAL"
            extraction_status = "UNRESOLVED_EXTERNAL"
        elif name in dependents_with_generated_mapping or d["kind"] in structural_kinds:
            confidence = "HIGH_EXPLICIT_AND_GENERATED"
            extraction_status = "VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES"
        else:
            confidence = "EXPLICIT_ONLY"
            extraction_status = "VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES"
        decl_layer_rows.append({
            "qualified_name": name, "source_file": d["source_file"], "kind": d["kind"],
            "layer": decl_metrics["layer"][name],
            "direct_internal_dependency_count": len(decl_metrics["dependencies"][name]),
            "transitive_internal_dependency_count": len(decl_metrics["transitive_dependencies"][name]),
            "direct_dependent_count": len(decl_metrics["dependents"][name]),
            "transitive_dependent_count": len(decl_metrics["transitive_dependents"][name]),
            "dependency_extraction_status": extraction_status,
            "dependency_extraction_confidence": confidence,
            "implicit_dependency_status": "UNRESOLVED_IMPLICIT_DEPENDENCY" if confidence != "UNRESOLVED_EXTERNAL" else "UNRESOLVED_EXTERNAL",
        })

    for d in declarations:
        source_command = (source / d["source_file"]).read_text(errors="replace")[d["start_char"]:d["end_char"]]
        normalized = " ".join(strip_comments(source_command).split())
        d["final_type_or_type_fingerprint"] = "source-command-sha256:" + sha256_bytes(normalized.encode())
        d["type_evidence_status"] = "SOURCE_COMMAND_FINGERPRINT; elaborated Check probe generated separately"
        d["structure_fields_if_any"] = json.dumps(d["structure_fields"], separators=(",", ":"))

    mathlib_revision = "NOT_APPLICABLE_TO_ROCQ_SOURCE_GRAPH"
    mathlib_lean_version = "UNAVAILABLE"
    if args.mathlib and (args.mathlib / ".git").exists():
        mathlib_revision = run(["git", "-C", str(args.mathlib), "rev-parse", "HEAD"]).stdout.strip()
        mathlib_lean_version = run(["lake", "env", "lean", "--version"], cwd=args.mathlib, check=False).stdout.strip()
    repo_commit = run(["git", "-C", str(args.repo_root), "rev-parse", "HEAD"]).stdout.strip()
    prosa_tree = run(["git", "-C", str(args.repo_root), "rev-parse", "HEAD:Prosa-fei/Prosa"]).stdout.strip()
    rocq_version = run(["opam", "exec", "--switch", args.opam_switch, "--", "rocq", "--version"]).stdout.strip()
    global_lean_version = run(["lean", "--version"], check=False).stdout.strip()
    mathcomp_packages = run(["opam", "list", "--switch", args.opam_switch, "--installed", "--columns=name,version", "--short"], check=False).stdout
    mathcomp_packages = [line.strip() for line in mathcomp_packages.splitlines() if "mathcomp" in line or "zify" in line]
    category_counts = Counter(r["category"] for r in inventory)
    manifest = {
        "authoritative_source": {"project": "Prosa", "version": "v0.6", "commit": commit,
                                 "git_tree": source_tree,
                                 "worktree": str(source), "v_file_count": len(paths)},
        "current_rts_repository_commit": repo_commit,
        "current_prosa_lean_tree_git_object": prosa_tree,
        "mathlib_revision_for_existing_lean_validation_environment": mathlib_revision,
        "toolchain": {"rocq": rocq_version, "rocq_opam_switch": args.opam_switch,
                      "mathcomp_packages": mathcomp_packages,
                      "lean_current_path": global_lean_version,
                      "lean_for_pinned_mathlib": mathlib_lean_version,
                      "mathlib_commit": mathlib_revision},
        "scope_policy": "Every .v at the pinned commit is inventoried exactly once; no source area is silently excluded.",
        "scope_categories": {"core_prosa": category_counts["CORE_PROSA"],
                             "core_aggregators": category_counts["CORE_AGGREGATOR"],
                             "implementation": category_counts["IMPLEMENTATION"],
                             "implementation_refinements": category_counts["IMPLEMENTATION_REFINEMENT"],
                             "library_examples": category_counts["LIBRARY_EXAMPLE"],
                             "tests": 0, "generated_sources": 0, "non_library_v_files": 0},
        "build_groups": {"main": sum(r["build_group"] == "main" for r in inventory),
                         "refinements": sum(r["build_group"] == "refinements" for r in inventory)},
        "coqdep": {"rules": len(paths), "stderr_sha256": sha256_bytes(args.coqdep_errors.read_bytes()),
                   "warnings": args.coqdep_errors.read_text(errors="replace").splitlines()},
        "declaration_dependency_policy": (
            "Theorem proof-body references are excluded. Explicit theorem-type and definition type/body references use .glob positions; "
            "constructors/projections and unambiguous HB symbols are mapped to public source owners. Missing .glob edges do not prove "
            "absence of implicit typeclass/canonical/HB dependencies; the file DAG remains authoritative."
        ),
    }
    (output / "scope_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    csv_write(output / "file_inventory.csv", list(inventory[0]), inventory)
    csv_write(output / "file_dag_edges.csv", list(file_edges[0]) if file_edges else [], file_edges)
    csv_write(output / "external_dependencies.csv",
              ["dependent_file", "dependent_module", "external_module", "edge_type", "classification"], external_rows)
    csv_write(output / "file_layers.csv", list(layer_rows[0]), layer_rows)
    csv_write(output / "declaration_inventory.csv",
              ["source_file", "declaration_name", "qualified_name", "kind", "final_type_or_type_fingerprint",
               "type_evidence_status", "structure_fields_if_any", "attributes", "computational_body_mode",
               "source_order", "source_line", "source_command_sha256"], declarations)
    csv_write(output / "declaration_dag_edges.csv",
              ["dependency", "dependent", "edge_type", "source_file", "reference_region",
               "evidence_categories", "generated_symbols", "mapping_methods", "implicit_dependency_status"],
              sorted(decl_edges.values(), key=lambda x: (x["dependent"], x["dependency"], x["edge_type"])))
    csv_write(output / "declaration_layers.csv", list(decl_layer_rows[0]) if decl_layer_rows else [], decl_layer_rows)

    file_json = {
        "edge_direction": "dependency -> dependent", "nodes": inventory, "edges": file_edges,
        "strongly_connected_components": file_metrics["components"], "cycles": file_metrics["cycles"],
        "condensation_edges": file_metrics["component_edges"], "longest_chain": file_metrics["longest_chain"],
    }
    layer_by_decl = {row["qualified_name"]: row for row in decl_layer_rows}
    decl_json = {
        "edge_direction": "dependency -> dependent", "proof_dependencies_included": False,
        "status": "VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES_WITH_DOCUMENTED_IMPLICIT_GENERATED_LIMITATIONS",
        "nodes": [{**{k: d[k] for k in ("qualified_name", "source_file", "kind", "source_order")},
                   "dependency_extraction_confidence": layer_by_decl[d["qualified_name"]]["dependency_extraction_confidence"],
                   "implicit_dependency_status": layer_by_decl[d["qualified_name"]]["implicit_dependency_status"]}
                  for d in declarations],
        "edges": sorted(decl_edges.values(), key=lambda x: (x["dependent"], x["dependency"], x["edge_type"])),
        "cycles": decl_metrics["cycles"], "longest_chain": decl_metrics["longest_chain"],
        "generated_symbol_mappings": sorted(generated_mappings.values(), key=lambda x: x["generated_symbol"]),
        "unresolved_generated_symbols": unresolved_generated_symbols,
        "unresolved_files": sorted(unresolved_decl_files),
    }
    (output / "file_dag.json").write_text(json.dumps(file_json, indent=2, sort_keys=True) + "\n")
    (output / "declaration_dag.json").write_text(json.dumps(decl_json, indent=2, sort_keys=True) + "\n")

    with (output / "file_dag.dot").open("w") as stream:
        stream.write('digraph prosa_v06_files {\n  rankdir="LR";\n  node [shape=box,fontsize=8];\n')
        for path in paths:
            category = inventory_by_file[path]["category"]
            color = "#ffd8a8" if category == "IMPLEMENTATION_REFINEMENT" else "#d0ebff" if category == "IMPLEMENTATION" else "#e6fcf5"
            stream.write(f'  "{path}" [fillcolor="{color}",style=filled];\n')
        for row in file_edges:
            style = "bold" if "REQUIRE_EXPORT" in row["edge_types"] else "solid"
            stream.write(f'  "{row["dependency_file"]}" -> "{row["dependent_file"]}" [style={style}];\n')
        stream.write("}\n")

    subsystem_edges = Counter()
    for a, b in graph_edges:
        subsystem_edges[(a.split("/", 1)[0], b.split("/", 1)[0])] += 1
    top_files = sorted(layer_rows, key=lambda r: (-r["transitive_dependent_count"], r["file"]))[:30]
    foundation_decls = sorted(decl_layer_rows, key=lambda r: (-r["transitive_dependent_count"], r["qualified_name"]))[:30]
    summary = ["# Prosa v0.6 File Dependency Summary", "", f"Pinned commit: `{commit}`.", "",
               "## Scope", "", f"All **{len(paths)}** `.v` files are present exactly once.", "",
               "| Category | Files |", "|---|---:|"]
    for category, count in sorted(Counter(r["category"] for r in inventory).items()): summary.append(f"| {category} | {count} |")
    summary += ["", "## Graph facts", "",
                f"- Internal file edges: **{len(graph_edges)}**.",
                f"- External require occurrences: **{len(external_rows)}** ({len(set(r['external_module'] for r in external_rows))} distinct modules).",
                f"- File layers: **{max(file_metrics['layer'].values()) + 1 if paths else 0}**.",
                f"- File cycles: **{len(file_metrics['cycles'])}**; the machine-readable JSON retains SCCs and condensation edges.",
                f"- Longest file dependency chain: **{len(file_metrics['longest_chain'])} nodes**.",
                f"- Public source declarations: **{len(declarations)}**.",
                f"- Declaration edges extracted: **{len(decl_edges)}**.",
                f"- Files with unresolved declaration reference extraction: **{len(unresolved_decl_files)}** (the refinement build boundary).", "",
                "## One longest file chain", "",
                " → ".join(f"`{node}`" for node in file_metrics["longest_chain"]), "",
                "## Derived subsystem edges", "", "| Dependency subsystem | Dependent subsystem | Edges |", "|---|---|---:|"]
    for (a, b), count in sorted(subsystem_edges.items()): summary.append(f"| {a} | {b} | {count} |")
    summary += ["", "## Highest file fan-out (transitive dependents)", "", "| File | Layer | Transitive dependents |", "|---|---:|---:|"]
    for row in top_files: summary.append(f"| `{row['file']}` | {row['layer']} | {row['transitive_dependent_count']} |")
    summary += ["", "## Highest declaration fan-out", "", "| Declaration | Kind | Transitive dependents | Extraction |", "|---|---|---:|---|"]
    for row in foundation_decls: summary.append(f"| `{row['qualified_name']}` | {row['kind']} | {row['transitive_dependent_count']} | {row['dependency_extraction_status']} |")
    summary += ["", "## Interpretation", "",
                "Layers and priority rankings are graph-derived. A lower layer is not automatically semantically more important; transitive dependent count identifies representation choices with broad downstream impact.",
                "The declaration graph is intentionally not a Lean-proof translation order: theorem proof-body references are excluded.",
                "Declaration edges establish explicit `.glob` references and mapped generated symbols only. Absence of an edge does not establish absence of an implicit typeclass/canonical/HB dependency; the file DAG remains authoritative for readiness.", ""]
    (output / "file_dag_summary.md").write_text("\n".join(summary))

    result = {"files": len(paths), "file_edges": len(graph_edges), "external_occurrences": len(external_rows),
              "external_modules": len(set(r["external_module"] for r in external_rows)),
              "file_layers": max(file_metrics["layer"].values()) + 1 if paths else 0,
              "file_cycles": len(file_metrics["cycles"]), "declarations": len(declarations),
              "declaration_edges": len(decl_edges), "unresolved_declaration_files": len(unresolved_decl_files),
              "declaration_cycles": len(decl_metrics["cycles"]),
              "generated_symbol_mappings": len(generated_mappings),
              "generated_symbol_edges": sum("GENERATED_SYMBOL_MAPPED" in row["evidence_categories"] for row in decl_edges.values()),
              "unresolved_generated_symbols": len(unresolved_generated_symbols),
              "declaration_confidence": dict(Counter(row["dependency_extraction_confidence"] for row in decl_layer_rows)),
              "unresolved_internal_imports": len(unresolved_internal)}
    (output / "generation_summary.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
