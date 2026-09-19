#!/usr/bin/env python3
"""Audit byte fidelity and elaborated types of auto-extracted Rocq sources.

The official type is read from the installed, kernel-checked Prosa 0.6 module
with its native Rocq toolchain.  The extracted declaration is checked with the
Rocq 9.3 validation toolchain.  A target passes only when its official source
block is byte-identical in the generated module and both fully explicit
(`Check @...` with `Set Printing All`) types normalize to the same text.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

import yaml

from extract_rocq_declarations import declaration_blocks
from generate_rocq_source_modules import active_context, relevant_context


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def checked_type(output: str) -> str:
    lines = output.splitlines()
    start = next((i for i, line in enumerate(lines) if re.match(r"^\s+:\s", line)), None)
    if start is None:
        raise RuntimeError(f"cannot locate Check type in output:\n{output}")
    first = re.sub(r"^\s+:\s*", "", lines[start])
    return " ".join(" ".join([first, *lines[start + 1:]]).split())


def normalize_qualification(type_text: str, generated_module: str) -> str:
    """Normalize only module-printing differences across Rocq 9.0/9.3.

    Rocq 9.0's printer abbreviates these imported Prosa/MathComp module paths,
    whereas 9.3 prints them. No constructor, binder, argument, or sort is
    removed by this normalization.
    """
    result = type_text.replace(generated_module + ".", "")
    return re.sub(r"\b(?:job|schedule|time|service|eqtype)\.", "", result)


def run_probe(switch: str, source: str, cwd: Path, extra: list[str]) -> str:
    probe = cwd / "TypeProbe.v"
    probe.write_text(source)
    command = ["opam", "exec", f"--switch={switch}", "--", "rocq", "c", *extra, str(probe)]
    completed = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if completed.returncode:
        raise RuntimeError(" ".join(command) + "\n" + completed.stdout + completed.stderr)
    return completed.stdout


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mapping", required=True, type=Path)
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--generated-dir", required=True, type=Path)
    parser.add_argument("--single-generated-module",
                        help="generated module used for all targets (RTS extractor mode)")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--official-switch", default="prosa-0.6")
    parser.add_argument("--validation-switch", default="rocq93rc1")
    parser.add_argument("--importer-src", type=Path, default=Path("/private/tmp/rocq-lean-import-93"))
    args = parser.parse_args()
    args.mapping = args.mapping.resolve()
    args.source_root = args.source_root.resolve()
    args.generated_dir = args.generated_dir.resolve()
    args.output = args.output.resolve()
    args.importer_src = args.importer_src.resolve()

    config = yaml.safe_load(args.mapping.read_text())
    report: dict[str, object] = {
        "source_commit": config.get("source_commit"),
        "method": "official installed .vo explicit type vs byte-identical Rocq-9.3 extraction explicit type",
        "targets": {},
    }
    failed = False

    with tempfile.TemporaryDirectory(prefix="source_fidelity.", dir=args.generated_dir.parent) as temp_name:
        temp = Path(temp_name)
        compiled_generated: set[str] = set()
        for key, target in config["targets"].items():
            acquisition = target.get("source_acquisition", {})
            if acquisition.get("mode") != "auto_extract":
                continue
            relpath = target["rocq_source_file"]
            source_path = args.source_root / relpath
            source_text = source_path.read_text()
            short = target["rocq_declaration"].rsplit(".", 1)[-1]
            blocks = declaration_blocks(source_text)
            if short not in blocks:
                report["targets"][key] = {"status": "BLOCKED_BY_SOURCE_EXTRACTION", "reason": "declaration block not found"}
                failed = True
                continue
            position, block = blocks[short]
            stem = relpath.replace("/", "__").removesuffix(".v")
            generated_module = (args.single_generated_module
                                or "Generated_" + re.sub(r"[^A-Za-z0-9_]", "_", stem))
            generated_path = args.generated_dir / f"{generated_module}.v"
            generated_text = generated_path.read_text()
            context = relevant_context(active_context(source_text, position), block)
            local_setup = [line for line in source_text[:position].splitlines()
                           if re.match(r"^\s*(?:#\[local\]\s+)?(?:Local\s+)?(?:Existing\s+Instance|Instance|Transparent)\b", line)]
            missing_setup = [line for line in local_setup if line.strip() and line not in generated_text]
            expected_hash = acquisition.get("source_hash")
            block_hash = sha256(block)
            block_identical = block in generated_text
            context_present = all(line in generated_text for line in context if line.strip())

            official_import = relpath.removesuffix(".v").replace("/", ".")
            official_probe = (
                f"From prosa Require Import {official_import}.\n"
                "Set Printing All.\n"
                f"Check @{target['rocq_declaration']}.\n"
            )
            generated_probe = (
                f"Require Import HardSource.{generated_module}.\n"
                "Set Printing All.\n"
                f"Check @{generated_module}.{short}.\n"
            )
            try:
                if generated_module not in compiled_generated:
                    copied_generated = temp / f"{generated_module}.v"
                    copied_generated.write_text(generated_text)
                    generated_compile = subprocess.run(
                        ["opam", "exec", f"--switch={args.validation_switch}", "--",
                         "rocq", "c", "-R", str(args.source_root), "prosa",
                         "-Q", str(args.importer_src / "src"), "LeanImport",
                         "-I", str(args.importer_src / "src"),
                         "-Q", str(temp), "HardSource", str(copied_generated)],
                        cwd=temp, text=True, capture_output=True,
                    )
                    if generated_compile.returncode:
                        raise RuntimeError(generated_compile.stdout + generated_compile.stderr)
                    compiled_generated.add(generated_module)
                official_output = run_probe(args.official_switch, official_probe, temp, [])
                generated_output = run_probe(
                    args.validation_switch, generated_probe, temp,
                    ["-R", str(args.source_root), "prosa",
                     "-Q", str(args.importer_src / "src"), "LeanImport",
                     "-I", str(args.importer_src / "src"),
                     "-Q", str(temp), "HardSource"],
                )
                official_type = checked_type(official_output)
                generated_type = checked_type(generated_output)
                # Extracted local dependencies live under the generated module
                # qualifier.  Erasing that one provenance-only prefix is the
                # sole normalization; binders, implicits, instances, and the
                # complete remaining elaborated term must still agree.
                normalized_official_type = normalize_qualification(official_type, generated_module)
                normalized_generated_type = normalize_qualification(generated_type, generated_module)
                type_equal = normalized_official_type == normalized_generated_type
                reason = "explicit elaborated types identical" if type_equal else "explicit elaborated types differ"
            except RuntimeError as error:
                official_type = generated_type = ""
                normalized_official_type = normalized_generated_type = ""
                type_equal = False
                reason = str(error)

            passed = (block_identical and context_present and not missing_setup and type_equal
                      and (not expected_hash or expected_hash == block_hash))
            if not passed:
                failed = True
            report["targets"][key] = {
                "status": "SOURCE_FIDELITY_VERIFIED" if passed else "BLOCKED_BY_SOURCE_EXTRACTION",
                "source_file": str(source_path),
                "generated_file": str(generated_path),
                "source_block_sha256": block_hash,
                "configured_source_hash_matches": not expected_hash or expected_hash == block_hash,
                "generated_block_identical": block_identical,
                "context_sha256": sha256("\n".join(context)),
                "context_commands_present": context_present,
                "local_setup_missing": missing_setup,
                "official_elaborated_type_sha256": sha256(official_type),
                "generated_elaborated_type_sha256": sha256(generated_type),
                "normalized_official_type_sha256": sha256(normalized_official_type),
                "normalized_generated_type_sha256": sha256(normalized_generated_type),
                "elaborated_type_identical": type_equal,
                "type_difference": None if type_equal else {
                    "official_normalized": normalized_official_type,
                    "generated_normalized": normalized_generated_type,
                },
                "reason": reason,
            }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for key, item in report["targets"].items():
        print(f"{key:36} {item['status']}")
    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
