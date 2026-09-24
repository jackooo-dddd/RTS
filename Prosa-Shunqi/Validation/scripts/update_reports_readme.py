#!/usr/bin/env python3
"""Refresh the human-readable 357-file inventory from accepted machine state.

This is a report renderer, not a semantic validator. It refuses inconsistent
inventory/order/coverage data and never infers acceptance from a Lean file.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import Counter
from datetime import datetime
from pathlib import Path
from urllib.parse import unquote, urlsplit
from zoneinfo import ZoneInfo


PROJECT = Path(__file__).resolve().parents[2]
DEPENDENCY = PROJECT / "Validation/planning/v06_dependency"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
ORDER = PROJECT / "v06_file_translation_order.md"
README = PROJECT / "Reports/README.md"
COMPLETION_EVIDENCE = PIPELINE / "reports_readme_completion_evidence.json"
ROW = re.compile(r"^(\d{3})\s+L(\d{2})\s+(\S+\.v)\s+(\d+)\s*$", re.M)
STATUS_BEGIN = "<!-- V06_STATUS_BEGIN -->"
STATUS_END = "<!-- V06_STATUS_END -->"
NAV_BEGIN = "<!-- V06_NAV_BEGIN -->"
NAV_END = "<!-- V06_NAV_END -->"
TABLE_BEGIN = "<!-- V06_FILE_TABLE_BEGIN -->"
TABLE_END = "<!-- V06_FILE_TABLE_END -->"
HK = ZoneInfo("Asia/Hong_Kong")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(f"REPORT_README_REJECTED: {message}")


def digest(path: Path) -> str:
    require(path.is_file(), f"missing {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def between(text: str, before: str, after: str, content: str) -> str:
    require(text.count(before) == text.count(after) == 1,
            f"missing/duplicate marker {before}")
    left, tail = text.split(before, 1)
    _, right = tail.split(after, 1)
    return left + before + "\n" + content.rstrip() + "\n" + after + right


def local_report(source: str) -> Path | None:
    path = Path(source)
    candidates = sorted(
        candidate for candidate in (PROJECT / "Reports/files" / path.parent).glob("*.md")
        if re.fullmatch(r"\d{4}-\d{2}-\d{2}_\d{6}_"
                        + re.escape(path.stem) + r"\.md", candidate.name)
    )
    require(len(candidates) <= 1, f"ambiguous canonical report: {source}")
    return candidates[0] if candidates else None


def link_for(source: str, required: bool) -> str:
    report = local_report(source)
    require(not required or report is not None, f"accepted file lacks canonical report: {source}")
    if report is None:
        return f"`{source}`"
    relative = report.relative_to(README.parent).as_posix()
    return f"[`{source}`]({relative})"


def check_links(content: str) -> None:
    """Reject broken local README links, including navigation anchors."""
    for target in re.findall(r"\]\(([^)]+)\)", content):
        parsed = urlsplit(target)
        if parsed.scheme or parsed.netloc:
            continue
        if parsed.path:
            path = README.parent / unquote(parsed.path)
            require(path.exists(), f"broken README link: {target}")
        if parsed.fragment:
            anchor = unquote(parsed.fragment)
            require(f'id="{anchor}"' in content or f"id='{anchor}'" in content,
                    f"broken README anchor: {target}")


def completion_evidence(accepted: set[str], first_status: dict[str, Path],
                        check: bool) -> dict[str, dict[str, str]]:
    """Freeze the first accepted machine-record time; never use report filenames.

    Older publishers did not include a JSON published_at. Their status file's
    creation/write time is recorded explicitly as a lower-strength time basis.
    The frozen record is content-bound so a later checkout does not silently
    replace publication times with its own file modification times.
    """
    if COMPLETION_EVIDENCE.exists():
        data = json.loads(COMPLETION_EVIDENCE.read_text())
        result = data["files"]
    else:
        require(not check, "completion-time evidence missing")
        result = {}
    for source in sorted(accepted):
        if source in result:
            entry = result[source]
            path = PROJECT / entry["status_file"]
            require(digest(path) == entry["status_sha256"],
                    f"completion evidence changed: {source}")
            datetime.fromisoformat(entry["completed_at"])
            if entry["time_basis"] == "canonical_report_acceptance_event":
                report = PROJECT / entry["report_file"]
                require(report.is_file()
                        and entry["report_time_text"] in report.read_text(),
                        f"canonical acceptance time evidence missing: {source}")
            continue
        require(not check, f"completion-time evidence missing for {source}")
        path = first_status[source]
        manifest = path.with_name(path.name.replace("_status.json", "_manifest.json"))
        published = json.loads(manifest.read_text()).get("published_at") if manifest.is_file() else None
        if published:
            moment = datetime.fromisoformat(published)
            basis = "manifest.published_at"
        else:
            moment = datetime.fromtimestamp(path.stat().st_mtime, HK)
            basis = "accepted_status_file_mtime"
        require(moment.tzinfo is not None, f"timezone missing: {source}")
        result[source] = {
            "completed_at": moment.astimezone(HK).isoformat(timespec="minutes"),
            "time_basis": basis,
            "status_file": path.relative_to(PROJECT).as_posix(),
            "status_sha256": digest(path),
        }
    require(set(result) == accepted,
            "completion evidence does not match current accepted file set")
    if not check:
        COMPLETION_EVIDENCE.write_text(json.dumps({
            "note": "Asia/Hong_Kong. Prefer manifest.published_at or an explicit "
                    "canonical-report acceptance event. Otherwise the first "
                    "ACCEPTED_V06_FILE status file mtime is a machine-record "
                    "proxy, not an independent event timestamp.",
            "files": result,
        }, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true",
                        help="fail if README differs; do not write")
    args = parser.parse_args()

    with (DEPENDENCY / "file_inventory.csv").open(newline="") as stream:
        files = list(csv.DictReader(stream))
    with (DEPENDENCY / "declaration_inventory.csv").open(newline="") as stream:
        declarations = list(csv.DictReader(stream))
    file_map = {row["file"]: row for row in files}
    counts = Counter(row["source_file"] for row in declarations)
    require(len(files) == len(file_map) == 357
            and len(declarations) == 2439
            and set(counts) <= set(file_map),
            "authoritative inventory is not the expected 357/2439 snapshot")

    order = [(int(rank), int(layer), source, int(mentioned))
             for rank, layer, source, mentioned in ROW.findall(ORDER.read_text())]
    require(len(order) == 357
            and [item[0] for item in order] == list(range(1, 358))
            and {item[2] for item in order} == set(file_map),
            "translation order does not cover authoritative files exactly once")
    for _, layer, source, mentioned in order:
        require(layer == int(file_map[source]["layer"])
                and mentioned == counts[source],
                f"order layer/declaration count differs from inventory: {source}")

    # Older partial and newer accepted statuses coexist. Select the most recent
    # explicit per-file record; do not infer status from production file presence.
    state: dict[str, tuple[int, str, Path]] = {}
    first_accepted: dict[str, tuple[int, Path]] = {}
    global_coverage: list[tuple[int, int, int, Path]] = []
    for path in sorted(PIPELINE.glob("*status.json")):
        data = json.loads(path.read_text())
        if "manifest_sha256" in data:
            manifest = path.with_name(path.name.replace("_status.json", "_manifest.json"))
            require(digest(manifest) == data["manifest_sha256"],
                    f"status/manifest hash mismatch: {path.name}")
        coverage = data.get("coverage", {})
        if "accepted_files" in coverage and "accepted_declarations" in coverage:
            global_coverage.append((int(coverage["accepted_files"]),
                                    int(coverage["accepted_declarations"]),
                                    path.stat().st_mtime_ns, path))
        entries = {
            source: value.get("status", "UNKNOWN")
            for source, value in data.get("per_file", {}).items()
        }
        entries.update({
            source: ("ACCEPTED_V06_FILE" if value.get("accepted") else "PARTIAL_V06_FILE")
            for source, value in data.get("file_gate", {}).items()
        })
        for source, status in entries.items():
            require(source in file_map, f"unknown file in status: {source}")
            candidate = (path.stat().st_mtime_ns, status, path)
            if source not in state or candidate[0] > state[source][0]:
                state[source] = candidate
            if status == "ACCEPTED_V06_FILE":
                first = (path.stat().st_mtime_ns, path)
                if source not in first_accepted or first[0] < first_accepted[source][0]:
                    first_accepted[source] = first
    require(global_coverage, "no machine-readable cumulative coverage")
    accepted = {source for source, (_, status, _) in state.items()
                if status == "ACCEPTED_V06_FILE"}
    accepted_declarations = sum(counts[source] for source in accepted)
    latest_files, latest_decls, _, latest_path = max(global_coverage)
    require(len(accepted) == latest_files
            and accepted_declarations == latest_decls,
            "per-file accepted evidence differs from cumulative machine coverage: "
            f"{len(accepted)}/{accepted_declarations} vs "
            f"{latest_files}/{latest_decls}")
    require(all(not source.startswith("implementation/refinements/") for source in accepted),
            "refinement boundary unexpectedly accepted")

    evidence = completion_evidence(
        accepted, {source: first_accepted[source][1] for source in accepted}, args.check)
    latest_source = max(accepted, key=lambda source: evidence[source]["completed_at"])
    latest_rank = next(rank for rank, _, source, _ in order if source == latest_source)

    today = max(entry["completed_at"] for entry in evidence.values())[:10]
    relative_status = latest_path.relative_to(PROJECT).as_posix()
    status_content = (
        f"截至 {today}，正式 machine state 记录 **{latest_files}/357 个文件、"
        f"{latest_decls}/2439 个 public declarations 已验收**。"
        f"依据：[最新累计 status](../{relative_status})。"
        "表中的“是”仅表示已有 `ACCEPTED_V06_FILE`；“否”可能是未开始、"
        "进行中或受阻，不能据此推断尚未翻译。零声明文件也只有通过模块接口验收才写“是”。"
    )
    nav = (
        "<details open>\n"
        "<summary><b>📊 Translation Status</b></summary>\n\n"
        "| Progress | Latest completed | Quick navigation |\n"
        "|---|---|---|\n"
        f"| **{latest_files}/357 files** · **{latest_decls}/2439 declarations** | "
        f"**Rank {latest_rank}** · `{latest_source}` | "
        "[🎯 Jump to latest completed](#latest-completed) · "
        "[✅ Finished](#finished-files) · "
        "[⏳ Unfinished](#unfinished-files) |\n\n"
        "</details>"
    )
    rows = ["<details open>",
            f"<summary><b>✅ Finished — {len(accepted)} files</b></summary>",
            "", "<a id=\"finished-files\"></a>", "",
            "| Rank | Layer | v0.6 source file | Public declarations | 验证完成 | 完成记录时间（月:日:时:分） |",
            "| ---: | ---: | --- | ---: | :---: | :---: |"]
    for rank, layer, source, _ in order:
        if source not in accepted:
            continue
        marker = '<a id="latest-completed"></a>' if source == latest_source else ""
        time = datetime.fromisoformat(evidence[source]["completed_at"]).strftime("%m:%d:%H:%M")
        rows.append(f"| {rank} | {layer} | {marker}{link_for(source, True)} | "
                    f"{counts[source]} | ✅ 是 | {time} |")
    rows.extend(["", "</details>", "", "<details open>",
                 f"<summary><b>⏳ Unfinished — {357 - len(accepted)} files</b></summary>",
                 "", "<a id=\"unfinished-files\"></a>", "",
                 "| Rank | Layer | v0.6 source file | Public declarations | 验证完成 |",
                 "| ---: | ---: | --- | ---: | :---: |"])
    for rank, layer, source, _ in order:
        if source in accepted:
            continue
        result = "⏸ 否（外部边界）" if source.startswith("implementation/refinements/") else "○ 否"
        rows.append(f"| {rank} | {layer} | {link_for(source, False)} | {counts[source]} | {result} |")
    rows.extend(["", "</details>"])

    original = README.read_text()
    rendered = between(original, STATUS_BEGIN, STATUS_END, status_content)
    rendered = between(rendered, NAV_BEGIN, NAV_END, nav)
    rendered = between(rendered, TABLE_BEGIN, TABLE_END, "\n".join(rows))
    check_links(rendered)
    if args.check:
        require(rendered == original, "README table/current coverage is stale")
    else:
        README.write_text(rendered)
    print(f"REPORT_README_OK files={len(accepted)}/357 "
          f"declarations={accepted_declarations}/2439 mode={'check' if args.check else 'write'}")


if __name__ == "__main__":
    main()
