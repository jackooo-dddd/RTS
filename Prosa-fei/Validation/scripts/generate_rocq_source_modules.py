#!/usr/bin/env python3
"""Generate compilable, target-scoped Rocq modules from pinned source files."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

import yaml

from extract_rocq_declarations import declaration_blocks


def import_prelude(text: str) -> list[str]:
    return [
        line for line in text.splitlines()
        if line.strip().startswith(("From ", "Require "))
    ]


def active_context(text: str, stop: int) -> list[str]:
    """Return active Section binder commands at byte offset stop."""
    frames: list[list[str]] = [[]]
    lines = text[:stop].splitlines()
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if re.match(r"^Section\s+[A-Za-z0-9_']+\.$", stripped):
            frames.append([])
        elif re.match(r"^End(?:\s+[A-Za-z0-9_']+)?\.$", stripped):
            if len(frames) > 1:
                frames.pop()
        elif re.match(
            r"^(?:Variable|Variables|Hypothesis|Hypotheses|Context|Local\s+Context)\b",
            stripped,
        ):
            command = [lines[i]]
            while not command[-1].rstrip().endswith("."):
                i += 1
                command.append(lines[i])
            frames[-1].extend(command)
        i += 1
    return [line for frame in frames for line in frame]


def relevant_context(lines: list[str], block: str) -> list[str]:
    commands: list[list[str]] = []
    current: list[str] = []
    for line in lines:
        if re.match(r"^\s*(?:Variable|Variables|Hypothesis|Hypotheses|Context|Local\s+Context)\b", line):
            if current:
                commands.append(current)
            current = [line]
        else:
            current.append(line)
    if current:
        commands.append(current)
    selected: list[list[str]] = []
    needed = block
    for command in reversed(commands):
        joined = " ".join(line.strip() for line in command)
        head = joined.split(":", 1)[0]
        head = re.sub(
            r"^(?:Variable|Variables|Hypothesis|Hypotheses|Context|Local\s+Context)\s+",
            "", head,
        )
        names = re.findall(r"[A-Za-z_][A-Za-z0-9_']*", head)
        if any(re.search(rf"\b{re.escape(name)}\b", needed) for name in names):
            selected.append(command)
            needed += " " + joined
    if selected:
        min_indent = min(len(command[0]) - len(command[0].lstrip()) for command in selected)
        selected_ids = {id(command) for command in selected}
        for command in commands:
            indent = len(command[0]) - len(command[0].lstrip())
            if indent >= min_indent and id(command) not in selected_ids:
                selected.append(command)
        selected.sort(key=lambda command: commands.index(command), reverse=True)
    result = []
    for command in reversed(selected):
        result.extend(command)
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mapping", required=True, type=Path)
    ap.add_argument("--source-root", required=True, type=Path)
    ap.add_argument("--output-dir", required=True, type=Path)
    args = ap.parse_args()
    config = yaml.safe_load(args.mapping.read_text())
    grouped: dict[str, list[tuple[str, dict]]] = {}
    for key, target in config["targets"].items():
        if target.get("source_acquisition", {}).get("mode") != "auto_extract":
            continue
        grouped.setdefault(target["rocq_source_file"], []).append((key, target))

    args.output_dir.mkdir(parents=True, exist_ok=True)
    for relpath, selected in sorted(grouped.items()):
        source = args.source_root / relpath
        text = source.read_text()
        blocks = declaration_blocks(text)
        wanted = {t["rocq_declaration"].rsplit(".", 1)[-1] for _, t in selected}
        changed = True
        while changed:
            changed = False
            for name in list(wanted):
                position, block = blocks[name]
                for dependency, (dep_position, _) in blocks.items():
                    if dep_position < position and re.search(rf"\b{re.escape(dependency)}\b", block):
                        if dependency not in wanted:
                            wanted.add(dependency)
                            changed = True

        ordered = sorted(((name, *blocks[name]) for name in wanted), key=lambda x: x[1])
        stem = relpath.replace("/", "__").removesuffix(".v")
        module = "Generated_" + re.sub(r"[^A-Za-z0-9_]", "_", stem)
        output = args.output_dir / f"{module}.v"
        lines = [*import_prelude(text), "", f"Module {module}.", ""]
        for index, (name, position, block) in enumerate(ordered):
            context = relevant_context(active_context(text, position), block)
            if context:
                lines.extend([f"Section ExtractedContext_{index}.", *context, ""])
            lines.extend([block.rstrip(), ""])
            if context:
                lines.extend([f"End ExtractedContext_{index}.", ""])
        lines.extend([f"End {module}.", ""])
        for _, target in selected:
            name = target["rocq_declaration"].rsplit(".", 1)[-1]
            lines.append(f"Check @{module}.{name}.")
            if target["kind"] == "theorem":
                lines.append(f"Print Assumptions {module}.{name}.")
        output.write_text("\n".join(lines) + "\n")
        print(output)


if __name__ == "__main__":
    main()
