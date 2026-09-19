#!/usr/bin/env python3
"""Generate a Rocq 9.3-buildable slice from configured official Prosa source.

Declaration blocks are copied byte-for-byte.  The only transformation is a
documented replacement of the legacy file's broad import prelude by the
minimal imports needed by the selected declarations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

import yaml


DECL_RE = re.compile(
    r"(?ms)^\s*(?:Lemma|Theorem|Fact|Corollary)\s+([A-Za-z0-9_']+)\b.*?^\s*(?:Qed|Defined)\.\s*$"
)


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def normalized_statement(block: str) -> str:
    head = re.split(r"(?m)^\s*Proof\.\s*$", block, maxsplit=1)[0]
    return " ".join(head.split())


def source_commit(root: Path, configured: str) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"], text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return configured


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mapping", required=True, type=Path)
    ap.add_argument("--source-root", required=True, type=Path)
    ap.add_argument("--output", type=Path)
    ap.add_argument("--metadata", type=Path)
    ap.add_argument("--list-lean-theorems", action="store_true")
    ap.add_argument("--list-lean-modules", action="store_true")
    args = ap.parse_args()

    config = yaml.safe_load(args.mapping.read_text())
    targets = [
        (key, value) for key, value in config["targets"].items()
        if value.get("kind") == "theorem"
        and value.get("lean_export_mode") == "statement_only"
    ]
    if args.list_lean_theorems:
        for _, target in targets:
            print(target["lean_declaration"])
        return
    if args.list_lean_modules:
        modules = {
            target["lean_source_file"].removesuffix(".lean").replace("/", ".")
            for _, target in targets
        }
        for module in sorted(modules):
            print(module)
        return
    if not args.output or not args.metadata:
        ap.error("--output and --metadata are required for extraction")

    grouped: dict[str, list[tuple[str, dict]]] = {}
    for key, target in targets:
        if target["source_acquisition"]["mode"] != "auto_extract":
            continue
        grouped.setdefault(target["rocq_source_file"], []).append((key, target))

    if len(grouped) != 1:
        raise SystemExit("prototype currently emits one generated module per source file")
    relpath, selected = next(iter(grouped.items()))
    source = args.source_root / relpath
    text = source.read_text()
    blocks = {m.group(1): (m.start(), m.group(0).lstrip("\n")) for m in DECL_RE.finditer(text)}

    wanted = {t["rocq_declaration"].rsplit(".", 1)[-1] for _, t in selected}
    changed = True
    while changed:
        changed = False
        for name in list(wanted):
            if name not in blocks:
                raise SystemExit(f"declaration not found in {source}: {name}")
            position, block = blocks[name]
            for dependency, (dep_position, _) in blocks.items():
                if dep_position < position and re.search(rf"\b{re.escape(dependency)}\b", block):
                    if dependency not in wanted:
                        wanted.add(dependency)
                        changed = True

    ordered = sorted(((name, *blocks[name]) for name in wanted), key=lambda x: x[1])
    first_position = ordered[0][1]
    prefix = text[:first_position]
    setup = []
    for line in prefix.splitlines():
        stripped = line.strip()
        if (stripped.startswith("#[local] Existing Instance")
                or stripped.startswith("Local Transparent")
                or stripped.startswith("Context ")):
            setup.append(line)

    configured_commit = selected[0][1]["source_acquisition"]["source_commit"]
    commit = source_commit(args.source_root, configured_commit)
    generated = [
        "From mathcomp Require Import ssreflect ssrbool eqtype fintype.",
        "From prosa Require Import behavior.service model.processor.ideal.",
        "",
        "(** AUTO-GENERATED from official Prosa source. Declaration blocks below",
        "    are copied verbatim; only the legacy broad import prelude is replaced. *)",
        "Module GeneratedOfficialProsa06.",
        "Section ScheduleClass.",
        *setup,
        "",
    ]
    for name, _, block in ordered:
        generated.extend([block.rstrip(), ""])
    generated.extend(["End ScheduleClass.", "End GeneratedOfficialProsa06.", ""])
    for _, target in selected:
        name = target["rocq_declaration"].rsplit(".", 1)[-1]
        generated.extend([
            f"Check @GeneratedOfficialProsa06.{name}.",
            f"Print Assumptions GeneratedOfficialProsa06.{name}.",
        ])

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(generated) + "\n")
    metadata = {
        "source_file": str(source),
        "source_commit": commit,
        "generated_file": str(args.output),
        "compatibility_transformation": "legacy broad imports replaced by minimal imports; declaration blocks unchanged",
        "declarations": {},
    }
    for key, target in selected:
        name = target["rocq_declaration"].rsplit(".", 1)[-1]
        block = blocks[name][1]
        actual_hash = sha256(block)
        expected_hash = target["source_acquisition"].get("source_hash")
        if expected_hash and actual_hash != expected_hash:
            raise SystemExit(
                f"official source fidelity failure for {name}: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        metadata["declarations"][key] = {
            "declaration": target["rocq_declaration"],
            "source_text_sha256": actual_hash,
            "normalized_statement": normalized_statement(block),
            "normalized_statement_sha256": sha256(normalized_statement(block)),
            "generated_block_identical": block in args.output.read_text(),
        }
    args.metadata.write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
