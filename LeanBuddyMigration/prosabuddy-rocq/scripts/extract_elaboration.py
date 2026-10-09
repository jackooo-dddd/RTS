#!/usr/bin/env python3
"""Extract elaborated Rocq kernel declarations into JSON.

The source file is processed normally by fcc.  A trusted coq-lsp plugin then
queries the completed document state and serializes the requested constants'
kernel types, universes, typing flags, and body kind.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence


PLUGIN_PACKAGE = "prosabuddy_elaboration_dump_plugin"


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Rocq elaboration and export selected kernel declarations as JSON."
    )
    parser.add_argument("source", type=Path, help="Rocq .v source file")
    parser.add_argument(
        "--target",
        action="append",
        required=True,
        help="Constant to export; repeat for multiple constants.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Output JSON path (default: SOURCE.elaboration.json)",
    )
    parser.add_argument(
        "--raw-type-output",
        type=Path,
        help=(
            "Also write the selected target's raw Serlib-serialized Constr.t "
            "as the JSON root. Requires exactly one --target."
        ),
    )
    parser.add_argument(
        "--raw-declaration-output",
        type=Path,
        help=(
            "Also write the selected target's raw Serlib-serialized "
            "Declarations.constant_body as the JSON root. Requires exactly "
            "one --target."
        ),
    )
    parser.add_argument(
        "-R",
        dest="recursive_load_paths",
        action="append",
        default=[],
        metavar="DIR,LOGICAL",
        help="Pass a recursive Rocq load path to fcc; repeat as needed.",
    )
    parser.add_argument(
        "-Q",
        dest="load_paths",
        action="append",
        default=[],
        metavar="DIR,LOGICAL",
        help="Pass a non-recursive Rocq load path to fcc; repeat as needed.",
    )
    parser.add_argument("--fcc", default="fcc", help="fcc executable")
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Do not rebuild the elaboration dump plugin before running.",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if (args.raw_type_output or args.raw_declaration_output) and len(args.target) != 1:
        print(
            "error: raw output requires exactly one --target",
            file=sys.stderr,
        )
        return 2

    source = args.source.expanduser().absolute()
    if not source.is_file():
        print(f"error: source file does not exist: {source}", file=sys.stderr)
        return 2

    script_dir = Path(__file__).resolve().parent
    plugin_dir = script_dir / PLUGIN_PACKAGE
    plugin_file = plugin_dir / "prosabuddy_elaboration_dump.cmxs"
    if not args.no_build:
        build = subprocess.run(
            [str(script_dir / "build_elaboration_dump_plugin.sh")],
            text=True,
            capture_output=True,
            check=False,
        )
        if build.returncode != 0:
            print(build.stdout, end="", file=sys.stderr)
            print(build.stderr, end="", file=sys.stderr)
            return build.returncode
    if not plugin_file.is_file():
        print(f"error: plugin was not built: {plugin_file}", file=sys.stderr)
        return 2

    output = (
        args.output.resolve()
        if args.output
        else Path(str(source) + ".elaboration.json")
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        output.unlink()

    environment = os.environ.copy()
    environment["PROSABUDDY_ELAB_TARGETS"] = ",".join(args.target)
    environment["PROSABUDDY_ELAB_OUTPUT"] = str(output)
    with tempfile.TemporaryDirectory(prefix="prosabuddy-elaboration-") as directory:
        temporary_source = Path(directory) / source.name
        shutil.copy2(source, temporary_source)
        command = [
            args.fcc,
            "--no_vo",
            f"--ocamlpath={script_dir}",
            f"--plugin={PLUGIN_PACKAGE}",
        ]
        for load_path in args.recursive_load_paths:
            command.extend(["-R", load_path])
        for load_path in args.load_paths:
            command.extend(["-Q", load_path])
        command.append(str(temporary_source))
        completed = subprocess.run(
            command,
            text=True,
            capture_output=True,
            check=False,
            env=environment,
        )
    if completed.returncode != 0:
        print(completed.stdout, end="", file=sys.stderr)
        print(completed.stderr, end="", file=sys.stderr)
        return completed.returncode
    if not output.is_file():
        print("error: fcc succeeded but the elaboration JSON was not created", file=sys.stderr)
        print(completed.stdout, end="", file=sys.stderr)
        print(completed.stderr, end="", file=sys.stderr)
        return 1

    try:
        payload = json.loads(output.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"error: invalid elaboration JSON: {exc}", file=sys.stderr)
        return 1

    errors = [item for item in payload.get("targets", []) if "error" in item]
    if errors:
        print(json.dumps(payload, ensure_ascii=False, indent=2), file=sys.stderr)
        return 1

    target = payload["targets"][0] if len(args.target) == 1 else None
    raw_outputs: dict[str, str] = {}
    if args.raw_type_output:
        raw_type_output = args.raw_type_output.expanduser().resolve()
        raw_type_output.parent.mkdir(parents=True, exist_ok=True)
        raw_type_output.write_text(
            json.dumps(target["type"], ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        raw_outputs["raw_type_output"] = str(raw_type_output)
    if args.raw_declaration_output:
        raw_declaration_output = args.raw_declaration_output.expanduser().resolve()
        raw_declaration_output.parent.mkdir(parents=True, exist_ok=True)
        raw_declaration_output.write_text(
            json.dumps(target["raw_declaration"], ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        raw_outputs["raw_declaration_output"] = str(raw_declaration_output)

    payload["source"] = str(source)
    payload["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    payload["logical_filename"] = source.name
    output.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    print(
        json.dumps(
            {
                "source": str(source),
                "output": str(output),
                "targets": [item.get("resolved_name") for item in payload["targets"]],
                **raw_outputs,
            },
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
