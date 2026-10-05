#!/usr/bin/env python3
from __future__ import annotations

import argparse
import shutil
import sys
from collections import deque
from pathlib import Path
import re


REQUIRE_RE = re.compile(
    r"(?ms)^\s*(?:Local\s+|Global\s+)?Require(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)"
)
FROM_REQUIRE_RE = re.compile(
    r"(?ms)^\s*(?:Local\s+|Global\s+)?From\s+([A-Za-z0-9_'.]+)\s+Require(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)"
)


def default_paths() -> tuple[Path, Path, Path]:
    repo_root = Path(__file__).resolve().parents[2]
    input_file = repo_root / "datasets_v06" / "casestudy_v06"
    source_root = Path("/home/tianchi/rtss26/prosa_v06")
    destination = repo_root / "test_tmp" / "prosa"
    return input_file, source_root, destination


def parse_args() -> argparse.Namespace:
    default_input, default_source, default_destination = default_paths()
    parser = argparse.ArgumentParser(
        description=(
            "Copy the Prosa modules referenced by a Coq file, or by all Coq "
            "files under a directory, into standalone projects."
        )
    )
    parser.add_argument(
        "input_path",
        nargs="?",
        type=Path,
        default=default_input,
        help=(
            "Path to a Coq file or to a directory whose .v files should be processed "
            f"(default: {default_input})."
        ),
    )
    parser.add_argument(
        "--source-root",
        type=Path,
        default=default_source,
        help=f"Path to the source Prosa root directory (default: {default_source}).",
    )
    parser.add_argument(
        "--destination",
        type=Path,
        default=default_destination,
        help=(
            "Path to the destination project root in single-file mode "
            f"(default: {default_destination}). Directory mode always writes to a "
            "sibling 'prosa' directory next to each .v file."
        ),
    )
    parser.add_argument(
        "--overwrite",
        action="store_true",
        help="Remove an existing destination directory before copying.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show the files that would be copied without changing the filesystem.",
    )
    return parser.parse_args()


def validate_paths(input_file: Path, source_root: Path, destination: Path, overwrite: bool) -> None:
    if not input_file.is_file():
        raise FileNotFoundError(f"Input Coq file not found: {input_file}")
    if not source_root.is_dir():
        raise FileNotFoundError(f"Source Prosa root not found: {source_root}")
    if destination.exists() and not overwrite:
        raise FileExistsError(
            f"Destination already exists: {destination}. Use --overwrite to replace it."
        )


def collect_entry_files(input_path: Path) -> list[Path]:
    if input_path.is_file():
        if input_path.suffix != ".v":
            raise ValueError(f"Input file is not a Coq source file: {input_path}")
        return [input_path]

    if not input_path.is_dir():
        raise FileNotFoundError(f"Input path not found: {input_path}")

    entry_files = sorted(
        path
        for path in input_path.rglob("*.v")
        if "prosa" not in path.parts
    )
    if not entry_files:
        raise FileNotFoundError(f"No Coq files found under directory: {input_path}")
    return entry_files


def strip_coq_comments(text: str) -> str:
    output: list[str] = []
    depth = 0
    index = 0

    while index < len(text):
        token = text[index : index + 2]
        if token == "(*":
            depth += 1
            index += 2
            continue
        if token == "*)" and depth > 0:
            depth -= 1
            index += 2
            continue
        if depth == 0:
            output.append(text[index])
        index += 1

    return "".join(output)


def extract_prosa_modules(text: str) -> list[str]:
    cleaned = strip_coq_comments(text)
    modules: list[str] = []

    for body in REQUIRE_RE.findall(cleaned):
        for token in body.split():
            if token.startswith("prosa."):
                modules.append(token)

    for prefix, body in FROM_REQUIRE_RE.findall(cleaned):
        if not prefix.startswith("prosa"):
            continue
        for token in body.split():
            module_name = token if token.startswith("prosa.") else f"{prefix}.{token}"
            modules.append(module_name)

    return list(dict.fromkeys(modules))


def module_to_relative_path(module_name: str) -> Path:
    if not module_name.startswith("prosa."):
        raise ValueError(f"Unsupported module outside Prosa namespace: {module_name}")
    parts = module_name.split(".")[1:]
    if not parts:
        raise ValueError(f"Invalid Prosa module name: {module_name}")
    return Path(*parts).with_suffix(".v")


def collect_transitive_modules(entry_file: Path, source_root: Path) -> tuple[dict[str, Path], list[str]]:
    pending = deque(extract_prosa_modules(entry_file.read_text(encoding="utf-8")))
    discovered: dict[str, Path] = {}
    missing: list[str] = []

    while pending:
        module_name = pending.popleft()
        if module_name in discovered:
            continue

        source_path = source_root / module_to_relative_path(module_name)
        if not source_path.is_file():
            missing.append(f"{module_name} -> {source_path}")
            continue

        discovered[module_name] = source_path
        child_modules = extract_prosa_modules(source_path.read_text(encoding="utf-8"))
        for child in child_modules:
            if child not in discovered:
                pending.append(child)

    return discovered, missing


def prepare_destination(destination: Path, overwrite: bool, dry_run: bool) -> None:
    if destination.exists() and overwrite:
        if dry_run:
            print(f"[DRY-RUN] Would remove existing destination: {destination}")
        else:
            shutil.rmtree(destination)
    if dry_run:
        print(f"[DRY-RUN] Would create destination root: {destination}")
    else:
        destination.mkdir(parents=True, exist_ok=True)


def copy_project_root_files(source_root: Path, destination: Path, dry_run: bool) -> int:
    copied = 0
    coqproject = source_root / "_CoqProject"
    if coqproject.is_file():
        target = destination / "_CoqProject"
        if dry_run:
            print(f"[DRY-RUN] Would copy {coqproject} -> {target}")
        else:
            shutil.copy2(coqproject, target)
        copied += 1
    return copied


def copy_modules(module_paths: dict[str, Path], source_root: Path, destination: Path, dry_run: bool) -> int:
    copied = 0
    for module_name, source_path in sorted(module_paths.items()):
        relative_path = source_path.relative_to(source_root)
        target_path = destination / relative_path
        if dry_run:
            print(f"[DRY-RUN] Would copy {module_name}: {source_path} -> {target_path}")
        else:
            target_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_path, target_path)
        copied += 1
    return copied


def _module_relative_paths(module_paths: dict[str, Path], source_root: Path) -> set[Path]:
    return {source_path.relative_to(source_root) for source_path in module_paths.values()}


def validate_minimal_prosa_module_set(
    module_paths: dict[str, Path],
    source_root: Path,
    destination: Path,
) -> int:
    expected = _module_relative_paths(module_paths, source_root)
    actual = {
        path.relative_to(destination)
        for path in destination.rglob("*.v")
        if path.is_file()
    }

    extra = sorted(actual - expected, key=str)
    missing = sorted(expected - actual, key=str)
    if extra or missing:
        details: list[str] = []
        if extra:
            details.append("extra files: " + ", ".join(str(path) for path in extra[:20]))
        if missing:
            details.append("missing files: " + ", ".join(str(path) for path in missing[:20]))
        raise RuntimeError(
            "Minimal Prosa copy does not match the transitive dependency closure ("
            + "; ".join(details)
            + ")."
        )
    return len(expected)


def validate_minimal_prosa_project(entry_file: Path, source_root: Path, destination: Path) -> int:
    modules, missing = collect_transitive_modules(entry_file, source_root)
    if missing:
        raise FileNotFoundError(
            "Missing source files for the following Prosa modules:\n  - "
            + "\n  - ".join(missing)
        )
    return validate_minimal_prosa_module_set(modules, source_root, destination)


def copy_minimal_prosa_project(
    entry_file: Path,
    source_root: Path,
    destination: Path,
    *,
    overwrite: bool = False,
    dry_run: bool = False,
) -> tuple[int, int]:
    validate_paths(entry_file, source_root, destination, overwrite)
    modules, missing = collect_transitive_modules(entry_file, source_root)
    if missing:
        raise FileNotFoundError(
            "Missing source files for the following Prosa modules:\n  - "
            + "\n  - ".join(missing)
        )

    prepare_destination(destination, overwrite, dry_run)
    copied_root_files = copy_project_root_files(source_root, destination, dry_run)
    copied_modules = copy_modules(modules, source_root, destination, dry_run)
    if not dry_run:
        validate_minimal_prosa_module_set(modules, source_root, destination)
    return copied_modules, copied_root_files


def copy_projects_for_input(
    input_path: Path,
    source_root: Path,
    destination: Path,
    *,
    overwrite: bool = False,
    dry_run: bool = False,
) -> tuple[list[tuple[Path, Path, int, int]], list[tuple[Path, str]]]:
    if not source_root.is_dir():
        raise FileNotFoundError(f"Source Prosa root not found: {source_root}")

    entry_files = collect_entry_files(input_path)
    batch_mode = input_path.is_dir()
    results: list[tuple[Path, Path, int, int]] = []
    errors: list[tuple[Path, str]] = []

    for entry_file in entry_files:
        target_destination = entry_file.parent / "prosa" if batch_mode else destination
        try:
            copied_modules, copied_root_files = copy_minimal_prosa_project(
                entry_file,
                source_root,
                target_destination,
                overwrite=overwrite,
                dry_run=dry_run,
            )
        except Exception as exc:
            errors.append((entry_file, str(exc)))
            continue

        results.append((entry_file, target_destination, copied_modules, copied_root_files))

    return results, errors


def main() -> int:
    args = parse_args()
    input_path = args.input_path.resolve()
    source_root = args.source_root.resolve()
    destination = args.destination.resolve()

    try:
        results, errors = copy_projects_for_input(
            input_path,
            source_root,
            destination,
            overwrite=args.overwrite,
            dry_run=args.dry_run,
        )
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    mode = "Dry run" if args.dry_run else "Copy"
    for entry_file, target_destination, copied_modules, copied_root_files in results:
        print(
            f"{mode}: input={entry_file}, modules={copied_modules}, "
            f"root_files={copied_root_files}, destination={target_destination}"
        )

    if errors:
        print("Errors:", file=sys.stderr)
        for entry_file, message in errors:
            print(f"  - {entry_file}: {message}", file=sys.stderr)
        return 1

    summary = "Dry run completed" if args.dry_run else "Copy completed"
    print(f"{summary}: processed={len(results)}, mode={'directory' if input_path.is_dir() else 'file'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())