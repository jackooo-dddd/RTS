#!/usr/bin/env python3
"""Authoritative planning evidence for the classic (ProsaBuddy f692cb7) validation family.

The classic counterpart of planning/v06_dependency/{generate_v06_inventory.py,
elaborate_declaration_types.py}.  Every output is derived from the pinned
ProsaBuddy checkout (`Validation/.work/prosabuddy-f692cb7`, verified commit,
tree and clean status) compiled UNCHANGED in ProsaBuddy's own toolchain, the
opam switch `prosa-0.6` (Rocq 9.0.1, MathComp 2.4) -- the environment in which
the case-study theorems are stated and will be proved.  The Rocq 9.3
validation build (compatibility prelude, recorded patches) is never used here.

  build      copy the case-study scope (classic-prosa/rocq93-port/scope_files.txt:
             util + classic, following the workspace's util symlink) into
             .work/classic_reference_rocq90/src and compile it with
             `rocq makefile` + `make` in the prosa-0.6 switch (`-R . prosa`, the
             warning flags of ProsaBuddy's own Makefile.case2015 project file)
  evidence   write planning/classic_dependency/:
               file_inventory.csv         scope files with sha256 (classic rows must equal
                                          casestudy-translation/file_order.csv, util rows
                                          the v0.6 file inventory)
               file_dag.json              direct `Require` edges between scope files
               declaration_inventory.csv  the named constants of the 49 case-study classic
                                          files, enumerated by Rocq (`Print Module`, nested
                                          modules recursively) and cross-checked against
                                          the source text (auto-generated schemes dropped)
               declaration_type_evidence.json  `Check @name` for every declaration, printed
                                          with every scope module `Require Import`ed (as the
                                          v0.6 evidence), normalized and sha256-hashed
               generation_summary.json

usage: classic_reference_evidence.py build|evidence|all
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[2]
V = PROJECT / "Validation"
CHECKOUT = V / ".work/prosabuddy-f692cb7"
SOURCE_ROOT = CHECKOUT / "prosaworkspace"
PIN = "f692cb7479780cf6009493f373a309e13165201c"
TREE = "24727b135eda27b7234119bf8d931d962d7c3593"
SWITCH = "prosa-0.6"
SCOPE = PROJECT / "classic-prosa/rocq93-port/scope_files.txt"
FILE_ORDER = PROJECT / "classic-prosa/casestudy-translation/file_order.csv"
V06_INVENTORY = V / "planning/v06_dependency/file_inventory.csv"
BUILD = V / ".work/classic_reference_rocq90"
OUT = V / "planning/classic_dependency"
FLAGS = "-w -notation-overriden,-parsing,-projection-no-head-constant,-ambiguous-paths"
DECL_KW = (r"(?:Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Corollary|Remark|Fact|Proposition|Instance|"
           r"Program\s+Definition|Program\s+Fixpoint|Program\s+Instance|Record|Structure|Inductive|Class|"
           r"Canonical(?:\s+Structure)?|Coercion|Example)")


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(CHECKOUT), *args], text=True).strip()


def verify_checkout() -> None:
    if git("rev-parse", "HEAD") != PIN or git("rev-parse", "HEAD^{tree}") != TREE:
        raise SystemExit("REJECTED: pinned ProsaBuddy checkout is not at the recorded commit/tree")
    if git("status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("REJECTED: pinned ProsaBuddy checkout is dirty")


def scope_files() -> list[str]:
    return [l.strip() for l in SCOPE.read_text().splitlines() if l.strip()]


def module_of(rel: str) -> str:
    return "prosa." + rel[:-2].replace("/", ".")


def rocq(args: list[str], cwd: Path, log: Path) -> int:
    with log.open("w") as out:
        return subprocess.run(["zsh", "-c", 'ulimit -s 65520 && exec "$@"', "_", "opam", "exec",
                               f"--switch={SWITCH}", "--", *args],
                              cwd=cwd, stdout=out, stderr=subprocess.STDOUT).returncode


def build() -> None:
    verify_checkout()
    if BUILD.exists():
        shutil.rmtree(BUILD)
    src = BUILD / "src"
    for rel in scope_files():
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE_ROOT / rel, src / rel)        # follows the util symlink
        if sha(src / rel) != sha(SOURCE_ROOT / rel):
            raise SystemExit(f"REJECTED: copy differs: {rel}")
    (src / "_CoqProject").write_text(f'-R . prosa\n-arg "{FLAGS}"\n')
    files = scope_files()
    if rocq(["rocq", "makefile", "-f", "_CoqProject", *files, "-o", "Makefile"], src, BUILD / "makefile.log"):
        raise SystemExit("REJECTED: rocq makefile failed")
    targets = [f[:-2] + ".vo" for f in files]
    if rocq(["make", f"-j{os.cpu_count() or 4}", *targets], src, BUILD / "build.log"):
        raise SystemExit("REJECTED: reference build failed (see build.log)")
    version = subprocess.check_output(["opam", "exec", f"--switch={SWITCH}", "--", "rocq", "--version"], text=True)
    (BUILD / "toolchain.txt").write_text(version)
    print(json.dumps({"built": len(files), "toolchain": version.splitlines()[0]}))


def strip_comments(text: str) -> str:
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("*)", i):
            depth -= 1; i += 2; continue
        out.append(text[i] if not depth else (" " if text[i] != "\n" else "\n")); i += 1
    return "".join(out)


def source_declarations(text: str) -> dict[str, tuple[str, str, int]]:
    """{module-relative name: (kind, command text, line)} from the source: tracks `Module M.` / `End M.`
    (sections do not change names)."""
    clean = strip_comments(text)
    stack: list[str] = []
    found: dict[str, tuple[str, str, int]] = {}
    for m in re.finditer(r"(?m)^\s*(?:(?:Local|Global|#\[[^\]]*\])\s+)*(Module(?:\s+Type)?|End|"
                         + DECL_KW + r")\s+([A-Za-z_][\w']*)", clean):
        kw, name = re.sub(r"\s+", " ", m.group(1)), m.group(2)
        line = clean.count("\n", 0, m.start()) + 1
        if kw.startswith("Module"):
            stack.append(name)
        elif kw == "End":
            if stack and stack[-1] == name:
                stack.pop()
        else:
            end = clean.find(".\n", m.end())
            found[".".join(stack + [name])] = (kw, clean[m.start():end + 1 if end >= 0 else m.end()].strip(), line)
    return found


def print_module_names(module: str, work: Path, cache: dict) -> list[str]:
    """Constant/inductive names of a compiled library module, nested modules recursively."""
    probe = work / "zz_print_module.v"
    probe.write_text(f"Set Printing Width 100000.\nRequire {module.split('|')[0]}.\n"
                     f"Print Module {module.split('|')[1]}.\n")
    log = work / "zz_print_module.log"
    require_ok = rocq(["rocq", "c", "-R", ".", "prosa", probe.name], work, log) == 0
    if not require_ok:
        raise SystemExit(f"REJECTED: Print Module failed for {module}: {log.read_text()[-2000:]}")
    out = log.read_text()
    names = []
    path = module.split("|")[1]
    m = re.search(r":= Struct (.*) End\s*$", out, re.S)
    body = m.group(1) if m else ""
    for kw, name in re.findall(r"(?:^|\. |Struct )(Definition|Parameter|Inductive|Module)\s+([A-Za-z_][\w']*)", body):
        if kw == "Module":
            names += print_module_names(f"{module.split('|')[0]}|{path}.{name}", work, cache)
        else:
            names.append(f"{path}.{name}")
    return names


def evidence() -> None:
    verify_checkout()
    src = BUILD / "src"
    if not (src / "classic/model/time.vo").is_file():
        raise SystemExit("REJECTED: run `build` first")
    OUT.mkdir(parents=True, exist_ok=True)
    files = scope_files()
    order = list(csv.DictReader(FILE_ORDER.open()))
    case_files = [r["source"].removeprefix("classic/") and r["source"] for r in order]
    v06 = {r["file"]: r["sha256"] for r in csv.DictReader(V06_INVENTORY.open())}

    # file inventory + DAG
    module_to_file = {module_of(f): f for f in files}
    edges, inv_rows = [], []
    for rel in files:
        h = sha(SOURCE_ROOT / rel)
        if rel.startswith("util/"):
            if v06.get(rel) != h:
                raise SystemExit(f"REJECTED: util file differs from the v0.6 inventory: {rel}")
            family = "V06_UTIL"
        else:
            family = "CLASSIC"
        row = next((r for r in order if r["source"] == rel), None)
        if row and row["sha256"] != h:
            raise SystemExit(f"REJECTED: classic file differs from file_order.csv: {rel}")
        text = strip_comments((SOURCE_ROOT / rel).read_text())
        deps = []
        for stmt in re.findall(r"(?:From\s+\S+\s+)?Require\s+(?:Import\s+|Export\s+)?((?:[\w.']+\s*)+)\.(?=\s)", text):
            for mod in stmt.split():
                if mod in module_to_file:
                    deps.append(mod)
        for mod in dict.fromkeys(deps):
            edges.append({"dependent_file": rel, "dependent_module": module_of(rel),
                          "dependency_file": module_to_file[mod], "dependency_module": mod})
        inv_rows.append({"file": rel, "module": module_of(rel), "family": family, "sha256": h,
                         "case_study_rank": row["rank"] if row else "",
                         "case_study_status": row["status"] if row else "",
                         "lines": len((SOURCE_ROOT / rel).read_text().splitlines())})
    with (OUT / "file_inventory.csv").open("w", newline="") as s:
        w = csv.DictWriter(s, fieldnames=list(inv_rows[0]), lineterminator="\n")
        w.writeheader(); w.writerows(inv_rows)
    (OUT / "file_dag.json").write_text(json.dumps({"edge_direction": "dependent_file requires dependency_file",
                                                   "edges": edges}, indent=2) + "\n")

    # declaration inventory (49 case-study classic files)
    decl_rows, unmatched = [], {}
    work = src
    for r in order:
        rel = r["source"]
        mod = module_of(rel)
        names = print_module_names(f"{mod}|{mod}", work, {})
        srcdecls = source_declarations((SOURCE_ROOT / rel).read_text())
        rel_names = [n[len(mod) + 1:] for n in names]
        kept = [n for n in rel_names if n in srcdecls]
        dropped = [n for n in rel_names if n not in srcdecls]
        missing = [n for n in srcdecls if n not in rel_names and srcdecls[n][0] not in ("Coercion",)]
        if dropped or missing:
            unmatched[rel] = {"generated_dropped": dropped, "source_not_in_module": missing}
        for i, n in enumerate(kept, 1):
            kind, cmd, line = srcdecls[n]
            decl_rows.append({"source_file": rel, "declaration_name": n, "qualified_name": f"{mod}.{n}",
                              "kind": kind, "final_type_or_type_fingerprint": "",
                              "type_evidence_status": "", "source_order": i, "source_line": line,
                              "source_command_sha256": hashlib.sha256(cmd.encode()).hexdigest()})

    # Check evidence with every scope module imported
    probe = src / "zz_classic_evidence.v"
    lines = ['Set Warnings "-notation-overridden".', "Set Printing Width 100000."]
    lines += [f"Require Import {module_of(f)}." for f in files]
    for d in decl_rows:
        q = d["qualified_name"]
        lines += [f'Goal True. idtac "BEGIN|{q}". Abort.', f"Check @{q}.", f'Goal True. idtac "END|{q}". Abort.']
    probe.write_text("\n".join(lines) + "\n")
    log = BUILD / "evidence_probe.log"
    if rocq(["rocq", "c", "-R", ".", "prosa", probe.name], src, log):
        raise SystemExit(f"REJECTED: evidence probe failed: {log.read_text()[-3000:]}")
    out = log.read_text(errors="replace")
    ev = {}
    for m in re.finditer(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$", out):
        rendered = m.group(2).strip()
        norm = " ".join(rendered.split())
        ev[m.group(1)] = {"rendered_check": rendered, "normalized_check": norm,
                          "sha256": hashlib.sha256(norm.encode()).hexdigest()}
    for d in decl_rows:
        item = ev.get(d["qualified_name"])
        if not item:
            raise SystemExit(f"REJECTED: no Check evidence for {d['qualified_name']}")
        d["final_type_or_type_fingerprint"] = "rocq-check-sha256:" + item["sha256"]
        d["type_evidence_status"] = "ELABORATED_ROCQ_CHECK"
    with (OUT / "declaration_inventory.csv").open("w", newline="") as s:
        w = csv.DictWriter(s, fieldnames=list(decl_rows[0]), lineterminator="\n")
        w.writeheader(); w.writerows(decl_rows)
    (OUT / "declaration_type_evidence.json").write_text(json.dumps(ev, indent=2, sort_keys=True) + "\n")
    summary = {
        "source": {"repository": "prosabuddy", "commit": PIN, "tree": TREE,
                   "workspace": "prosaworkspace", "checkout": str(CHECKOUT.relative_to(PROJECT))},
        "toolchain": (BUILD / "toolchain.txt").read_text().splitlines()[0], "opam_switch": SWITCH,
        "scope_files": len(files), "case_study_files": len(order),
        "declarations": len(decl_rows),
        "declarations_per_file": {r["source"]: sum(1 for d in decl_rows if d["source_file"] == r["source"])
                                  for r in order},
        "unmatched_names": unmatched,
        "script": "Validation/scripts/classic_reference_evidence.py",
        "script_sha256": sha(Path(__file__)),
    }
    (OUT / "generation_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    # coverage denominators of the classic status chain, and the recorded compatibility prelude
    (OUT / "scope.json").write_text(json.dumps({
        "case_study_files": len(order), "case_study_declarations": len(decl_rows),
        "file_order": str(FILE_ORDER.relative_to(PROJECT)), "file_order_sha256": sha(FILE_ORDER)}, indent=2) + "\n")
    prelude = PROJECT / "classic-prosa/rocq93-port/Rocq90Compat.v"
    (OUT / "prelude.json").write_text(json.dumps({
        "file": str(prelude.relative_to(PROJECT)), "sha256": sha(prelude),
        "purpose": "restores two Rocq 9.0 defaults for classic sources under Rocq 9.3: "
                   "#[export] Set SsrOldRewriteGoalsOrder and the 9.0 intuition_solver; no source edits",
        "flags": "-Q <compat> Compat -ri Compat.Rocq90Compat (classic/ files only)"}, indent=2) + "\n")
    print(json.dumps({k: summary[k] for k in ("scope_files", "case_study_files", "declarations")}))
    if unmatched:
        print("UNMATCHED (review):", json.dumps(unmatched, indent=1))


if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else "all"
    if stage in ("build", "all"):
        build()
    if stage in ("evidence", "all"):
        evidence()
