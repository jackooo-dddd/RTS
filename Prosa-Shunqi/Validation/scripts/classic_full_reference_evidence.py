#!/usr/bin/env python3
"""Authoritative planning evidence for the WHOLE classic folder (comprehensive-classic validation).

Additive companion of classic_reference_evidence.py (which covers the 49 case-study files and is left
unchanged, as are its outputs in planning/classic_dependency).  Every output here is derived from the
pinned ProsaBuddy checkout (`Validation/.work/prosabuddy-f692cb7`, verified commit, tree and clean
status) compiled UNCHANGED in ProsaBuddy's own toolchain, the opam switch `prosa-0.6` (Rocq 9.0.1,
MathComp 2.4).  The Rocq 9.3 validation build is never used here.

Scope: the 190 classic files of classic-prosa/comprehensive-classic/file_order.csv plus every util
file they transitively Require.

  build      copy the scope into .work/classic_full_reference_rocq90/src (hash-checked) and compile it
             with `rocq makefile` + `make` in the prosa-0.6 switch (`-R . prosa`, ProsaBuddy's flags)
  evidence   write planning/classic_full_dependency/:
               file_inventory.csv         scope files with sha256 (classic rows must equal the
                                          comprehensive file_order.csv, util rows the v0.6 inventory)
               file_dag.json              direct `Require` edges between scope files
               declaration_inventory.csv  named constants of all 190 classic files (`Print Module`,
                                          nested modules recursively, cross-checked against the source)
               declaration_type_evidence.json  `Check @name` for every declaration, printed in the
                                          display context of the run fingerprint probes written by
                                          classic_mkfile.py: every file of the declaration's own
                                          dependency closure `Require Import`ed (alphabetical), then
                                          MathComp's notation modules
               generation_summary.json    (incl. a comparison with the case-study evidence)
               scope.json, prelude.json   coverage denominators (190 files) and the recorded prelude

usage: classic_full_reference_evidence.py build|evidence|all
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import classic_reference_evidence as R  # noqa: E402  (shared checkout/source helpers; unchanged)

PROJECT = R.PROJECT
V = R.V
SOURCE_ROOT = R.SOURCE_ROOT
FILE_ORDER = PROJECT / "classic-prosa/comprehensive-classic/file_order.csv"
BUILD = V / ".work/classic_full_reference_rocq90"
OUT = V / "planning/classic_full_dependency"
CASE_DEP = V / "planning/classic_dependency"
DISPLAY = "From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path."


def classic_files() -> list[str]:
    return [r["source"] for r in csv.DictReader(FILE_ORDER.open())]


def requires(rel: str, known: dict[str, str]) -> list[str]:
    text = R.strip_comments((SOURCE_ROOT / rel).read_text())
    deps = []
    for m in re.finditer(r"\bRequire\b", text):
        end = re.search(r"\.(\s|$)", text[m.end():])
        command = text[m.end(): m.end() + (end.start() if end else 0)]
        for mod in command.split():
            if mod in known:
                deps.append(known[mod])
    return list(dict.fromkeys(deps))


def source_declarations(text: str) -> dict[str, tuple[str, str, int]]:
    """{module-relative name: (kind, command text, line)} from the source (corrected scanner of the
    case-study script, which is left unchanged): `Section` and `Module` share one stack, so a `Section`
    named like its enclosing `Module` closes the right block; a module alias / signature-ascribed module
    (`Module X := M.`, `Module X : S := M.`) does not open a block."""
    clean = R.strip_comments(text)
    stack: list[tuple[str, str]] = []
    found: dict[str, tuple[str, str, int]] = {}
    for m in re.finditer(r"(?m)^\s*(?:(?:Local|Global|#\[[^\]]*\])\s+)*(Module(?:\s+Type)?|Section|End|"
                         + R.DECL_KW + r")\s+([A-Za-z_][\w']*)", clean):
        kw, name = re.sub(r"\s+", " ", m.group(1)), m.group(2)
        line = clean.count("\n", 0, m.start()) + 1
        end = re.search(r"\.(\s|$)", clean[m.end():])
        command = clean[m.end(): m.end() + (end.start() if end else 0)]
        if kw.startswith("Module"):
            if ":=" not in command:
                stack.append(("M", name))
        elif kw == "Section":
            stack.append(("S", name))
        elif kw == "End":
            if stack and stack[-1][1] == name:
                stack.pop()
        else:
            stop = clean.find(".\n", m.end())
            path = [n for k, n in stack if k == "M"]
            found[".".join(path + [name])] = (kw, clean[m.start():stop + 1 if stop >= 0 else m.end()].strip(), line)
    return found


def print_module_names(module: str, work: Path) -> list[str]:
    """R.print_module_names, also listing `Record` entries (record types; their projections are listed by Rocq
    as `Definition`s and are covered by the record's certificate, as in the accepted v0.6/case-study policy)."""
    probe = work / "zz_print_module.v"
    probe.write_text(f"Set Printing Width 100000.\nRequire {module.split('|')[0]}.\n"
                     f"Print Module {module.split('|')[1]}.\n")
    log = work / "zz_print_module.log"
    if R.rocq(["rocq", "c", "-R", ".", "prosa", probe.name], work, log) != 0:
        raise SystemExit(f"REJECTED: Print Module failed for {module}: {log.read_text()[-2000:]}")
    out = log.read_text()
    names = []
    path = module.split("|")[1]
    m = re.search(r":=\s*Struct\s(.*)\sEnd\s*$", out, re.S)
    body = m.group(1) if m else ""
    for kw, name in re.findall(r"(?<![\w.'])(Definition|Parameter|Inductive|Record|Module)\s+([A-Za-z_][\w']*)", body):
        if kw == "Module":
            names += print_module_names(f"{module.split('|')[0]}|{path}.{name}", work)
        else:
            names.append(f"{path}.{name}")
    return names


def scope_files() -> list[str]:
    """Classic files (file_order) + the util files they transitively Require, util first (sorted)."""
    candidates = {R.module_of(str(p.relative_to(SOURCE_ROOT))): str(p.relative_to(SOURCE_ROOT))
                  for d in ("util", "classic") for p in sorted((SOURCE_ROOT / d).rglob("*.v"))}
    seen: set[str] = set()
    todo = list(classic_files())
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        todo += requires(f, candidates)
    util = sorted(f for f in seen if f.startswith("util/"))
    classic = classic_files()
    extra = sorted(f for f in seen if not f.startswith("util/") and f not in classic)
    if extra:
        raise SystemExit(f"REJECTED: classic files required but not in file_order.csv: {extra}")
    return util + classic


def build() -> None:
    R.verify_checkout()
    if BUILD.exists():
        shutil.rmtree(BUILD)
    src = BUILD / "src"
    files = scope_files()
    for rel in files:
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE_ROOT / rel, src / rel)        # follows the util symlink
        if R.sha(src / rel) != R.sha(SOURCE_ROOT / rel):
            raise SystemExit(f"REJECTED: copy differs: {rel}")
    (src / "_CoqProject").write_text(f'-R . prosa\n-arg "{R.FLAGS}"\n')
    if R.rocq(["rocq", "makefile", "-f", "_CoqProject", *files, "-o", "Makefile"], src, BUILD / "makefile.log"):
        raise SystemExit("REJECTED: rocq makefile failed")
    targets = [f[:-2] + ".vo" for f in files]
    if R.rocq(["make", f"-j{os.cpu_count() or 4}", *targets], src, BUILD / "build.log"):
        raise SystemExit("REJECTED: reference build failed (see build.log)")
    version = subprocess.check_output(["opam", "exec", f"--switch={R.SWITCH}", "--", "rocq", "--version"], text=True)
    (BUILD / "toolchain.txt").write_text(version)
    (BUILD / "scope_files.txt").write_text("\n".join(files) + "\n")
    print(json.dumps({"built": len(files), "toolchain": version.splitlines()[0]}))


def closure(source: str, deps: dict[str, list[str]]) -> list[str]:
    seen: set[str] = set()

    def visit(f: str) -> None:
        if f in seen:
            return
        seen.add(f)
        for d in deps.get(f, []):
            visit(d)
    visit(source)
    return sorted(seen)


def evidence() -> None:
    R.verify_checkout()
    src = BUILD / "src"
    files = (BUILD / "scope_files.txt").read_text().split()
    if files != scope_files() or not all((src / (f[:-2] + ".vo")).is_file() for f in files):
        raise SystemExit("REJECTED: run `build` first (scope changed or .vo missing)")
    for rel in files:
        if R.sha(src / rel) != R.sha(SOURCE_ROOT / rel):
            raise SystemExit(f"REJECTED: build copy differs from the checkout: {rel}")
    OUT.mkdir(parents=True, exist_ok=True)
    order = list(csv.DictReader(FILE_ORDER.open()))
    v06 = {r["file"]: r["sha256"] for r in csv.DictReader(R.V06_INVENTORY.open())}

    # file inventory + DAG
    module_to_file = {R.module_of(f): f for f in files}
    edges, inv_rows, deps = [], [], {}
    for rel in files:
        h = R.sha(SOURCE_ROOT / rel)
        if rel.startswith("util/"):
            if v06.get(rel) != h:
                raise SystemExit(f"REJECTED: util file differs from the v0.6 inventory: {rel}")
            family = "V06_UTIL"
        else:
            family = "CLASSIC"
        row = next((r for r in order if r["source"] == rel), None)
        if family == "CLASSIC" and (row is None or row["sha256"] != h):
            raise SystemExit(f"REJECTED: classic file differs from file_order.csv: {rel}")
        deps[rel] = requires(rel, module_to_file)
        for dep in deps[rel]:
            edges.append({"dependent_file": rel, "dependent_module": R.module_of(rel),
                          "dependency_file": dep, "dependency_module": R.module_of(dep)})
        inv_rows.append({"file": rel, "module": R.module_of(rel), "family": family, "sha256": h,
                         "comprehensive_rank": row["rank"] if row else "",
                         "lines": len((SOURCE_ROOT / rel).read_text().splitlines())})
    with (OUT / "file_inventory.csv").open("w", newline="") as s:
        w = csv.DictWriter(s, fieldnames=list(inv_rows[0]), lineterminator="\n")
        w.writeheader(); w.writerows(inv_rows)
    (OUT / "file_dag.json").write_text(json.dumps({"edge_direction": "dependent_file requires dependency_file",
                                                   "edges": edges}, indent=2) + "\n")

    # declaration inventory (all 190 classic files)
    decl_rows, unmatched = [], {}
    for r in order:
        rel = r["source"]
        mod = R.module_of(rel)
        names = print_module_names(f"{mod}|{mod}", src)
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

    # Check evidence: one probe per classic file, in the run probe's display context
    ev = {}
    logs = BUILD / "evidence_logs"
    logs.mkdir(exist_ok=True)
    for r in order:
        rel = r["source"]
        qs = [d["qualified_name"] for d in decl_rows if d["source_file"] == rel]
        if not qs:
            continue
        stem = rel[:-2].replace("/", "__")
        lines = ['Set Warnings "-notation-overridden,-missing-proof-command".', "Set Printing Width 100000."]
        lines += [f"Require Import {R.module_of(f)}." for f in closure(rel, deps)]
        lines += [DISPLAY]
        for q in qs:
            lines += [f'Goal True. idtac "BEGIN|{q}". Abort.', f"Check @{q}.", f'Goal True. idtac "END|{q}". Abort.']
        probe = src / f"zz_full_evidence_{stem}.v"
        probe.write_text("\n".join(lines) + "\n")
        log = logs / f"{stem}.log"
        if R.rocq(["rocq", "c", "-R", ".", "prosa", probe.name], src, log):
            raise SystemExit(f"REJECTED: evidence probe failed for {rel}: {log.read_text()[-3000:]}")
        out = log.read_text(errors="replace")
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

    # comparison with the case-study evidence (informational: display context differs)
    case_ev = json.loads((CASE_DEP / "declaration_type_evidence.json").read_text())
    case_inv = [r["qualified_name"] for r in csv.DictReader((CASE_DEP / "declaration_inventory.csv").open())]
    missing_case = [q for q in case_inv if q not in ev]
    same = sum(1 for q in case_inv if q in ev and ev[q]["normalized_check"] == case_ev[q]["normalized_check"])
    differ = [q for q in case_inv if q in ev and ev[q]["normalized_check"] != case_ev[q]["normalized_check"]]
    if missing_case:
        raise SystemExit(f"REJECTED: case-study declarations missing from the full inventory: {missing_case}")
    summary = {
        "source": {"repository": "prosabuddy", "commit": R.PIN, "tree": R.TREE,
                   "workspace": "prosaworkspace", "checkout": str(R.CHECKOUT.relative_to(PROJECT))},
        "toolchain": (BUILD / "toolchain.txt").read_text().splitlines()[0], "opam_switch": R.SWITCH,
        "scope_files": len(files), "classic_files": len(order), "declarations": len(decl_rows),
        "declarations_per_file": {r["source"]: sum(1 for d in decl_rows if d["source_file"] == r["source"])
                                  for r in order},
        "unmatched_names": unmatched,
        "display_context": "per declaration: its file's dependency closure Require Import-ed (alphabetical), "
                           "then `" + DISPLAY + "` (the classic_mkfile.py fingerprint-probe header)",
        "case_study_comparison": {"declarations": len(case_inv), "identical_normalized_check": same,
                                  "display_differs": differ},
        "script": "Validation/scripts/classic_full_reference_evidence.py",
        "script_sha256": R.sha(Path(__file__)),
    }
    (OUT / "generation_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (OUT / "scope.json").write_text(json.dumps({
        "case_study_files": len(order), "case_study_declarations": len(decl_rows),
        "note": "coverage denominators of the comprehensive classic chain (the keys keep the pipeline's names)",
        "file_order": str(FILE_ORDER.relative_to(PROJECT)), "file_order_sha256": R.sha(FILE_ORDER)}, indent=2) + "\n")
    shutil.copyfile(CASE_DEP / "prelude.json", OUT / "prelude.json")
    print(json.dumps({k: summary[k] for k in ("scope_files", "classic_files", "declarations")}))
    print(json.dumps(summary["case_study_comparison"] | {"display_differs": len(differ)}))
    if unmatched:
        print("UNMATCHED (review):", json.dumps(unmatched, indent=1))


if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else "all"
    if stage in ("build", "all"):
        build()
    if stage in ("evidence", "all"):
        evidence()
