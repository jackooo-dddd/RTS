#!/usr/bin/env python3
"""Generate the validation artifacts of one classic-family file from a small config.

Classic counterpart of the session tool mkfile.py used for v0.6.  Everything that
is derivable is derived from the planning inputs (planning/classic_dependency) and the
compiled Lean translation; the certificate chain itself is written by hand.

  config (JSON):
    rank, slug, tag, export_name, source            (source = classic/... .v)
    production                                       (Prosa/Classic/... .lean)
    fixtures         [Lean fixture module names under Validation/fixtures/translation_order]
    export_module    module the exporter loads (a fixture, or the production module)
    interface_theorems  fully qualified Lean theorems exported with their proofs
    extra_targets    other fully qualified Lean constants to export (definitions)
    computational    declaration names (module-relative) that are definitions
    chain            certificate modules (in order; the last one holds the principal certs)
    principal        {declaration: [certificate, ...]} for non-default principal certs
    helpers          extra certificate names to audit
    base_run, base_checks, extra_olean_artifacts     as in the pipeline spec
    previous_status, previous_files, previous_decls
    input_relations, lean_representation_note, export_env (optional)
    prop_sprop_foundation, importer_foundation, rocq_sprop_uip   (optional: replace the
                     default allowlists by the names actually observed in Print Assumptions)

writes: tooling/classic/file_specs/<slug>.json, tooling/classic/<slug>_export_config.json,
        tooling/classic/closures/<slug>.txt, fixtures/translation_order/<Name>TypeFingerprintProbe.v,
        <Name>LeanTypeAudit.lean, <Name>ImportedTypeAudit.v, and in certificates/<slug>/:
        Imported<export_name>.v, <slug>_lean_axiom_config.json (actual axioms of the built
        declarations), <slug>_assumption_config.json, <Name>AssumptionAudit.v.

usage: classic_mkfile.py CONFIG.json
"""
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[2]
V = PROJECT / "Validation"
DEP = V / "planning/classic_dependency"
FULL_DEP = V / "planning/classic_full_dependency"   # config `classic_scope: "full"` (comprehensive classic)


def lean_ns(source: str) -> str:
    return "Prosa." + ".".join("".join(w[:1].upper() + w[1:] for w in part.split("_"))
                               for part in source[:-2].split("/"))


def closure(source: str) -> list[str]:
    edges = json.loads((DEP / "file_dag.json").read_text())["edges"]
    deps: dict[str, list[str]] = {}
    for e in edges:
        deps.setdefault(e["dependent_file"], []).append(e["dependency_file"])
    order: list[str] = []
    seen: set[str] = set()

    def visit(f: str) -> None:
        if f in seen:
            return
        seen.add(f)
        for d in sorted(deps.get(f, [])):
            visit(d)
        order.append(f)
    visit(source)
    return order


def prosa_import_closure(modules: list[str]) -> list[str]:
    """Transitive `Prosa.*` imports (dependency order) of the given Lean modules, excluding themselves."""
    order: list[str] = []
    seen: set[str] = set()

    def visit(m: str) -> None:
        if m in seen:
            return
        seen.add(m)
        path = PROJECT / (m.replace(".", "/") + ".lean")
        for imp in re.findall(r"^import (Prosa\.\S+)$", path.read_text(), re.M):
            visit(imp)
        order.append(m)
    for m in modules:
        visit(m)
    return [m for m in order if m not in modules]


def auto_olean_artifacts(modules: list[str]) -> list[dict]:
    """Every Prosa dependency olean of the run, bound to the manifest that accepted it: a classic module by its
    classic manifest (copied from its accepted run), a v0.6 module by `v06_file` (copied from any run holding the
    accepted bytes)."""
    sys.path.insert(0, str(V / "scripts"))
    import translation_file_pipeline as P
    P.FAMILY, P.PIPE = "classic", P.CLASSIC["pipe"]
    arts = []
    for m in prosa_import_closure(modules):
        rel = m.replace(".", "/") + ".olean"
        src = re.search(r"^-- source: (\S+\.v)$", (PROJECT / (m.replace(".", "/") + ".lean")).read_text(), re.M)
        if not src:
            raise SystemExit(f"no source header in {m}")
        if m.startswith("Prosa.Classic."):
            slug = src.group(1)[:-2].replace("/", "_")
            arts.append({"from": f"{slug}_final/olean/{rel}", "to": rel, "manifest": slug,
                         "key": "production_olean_sha256"})
        else:
            want = P.v06_file_olean_hash(src.group(1))
            run = next((r for r in sorted((V / ".work/experiments").glob("*/olean/" + rel))
                        if hashlib.sha256(r.read_bytes()).hexdigest() == want), None)
            if run is None:
                raise SystemExit(f"no run holds the accepted olean of {m}")
            arts.append({"from": str(run.relative_to(V / ".work/experiments")), "to": rel,
                         "v06_file": src.group(1)})
    return arts


def previous_counts(cfg: dict) -> dict:
    """The formal baseline counts, read from the previous status file (a config value must agree)."""
    if cfg.get("previous_status") is None:
        return {"previous_files": 0, "previous_decls": 0}
    cov = json.loads((V / "planning/classic_pipeline" / cfg["previous_status"]).read_text())["coverage"]
    got = {"previous_files": cov["accepted_files"], "previous_decls": cov["accepted_declarations"]}
    for k, v in got.items():
        if k in cfg and cfg[k] != v:
            raise SystemExit(f"{k}: config says {cfg[k]}, {cfg['previous_status']} says {v}")
    return got


def actual_axioms(module: str, names: list[str]) -> dict[str, list[str]]:
    probe = PROJECT / f".lake/classic_mkfile_axioms_{os.getpid()}.lean"   # per-process: concurrent prepares
    prints = "".join(f"#print axioms {n}\n" for n in names)
    if module.startswith("Validation."):   # a fixture is not a Lake target: audit a copy of its source
        probe.write_text((PROJECT / (module.replace(".", "/") + ".lean")).read_text() + "\n" + prints)
    else:
        probe.write_text(f"import {module}\n" + prints)
    out = subprocess.run(["lake", "env", "lean", str(probe)], cwd=PROJECT, capture_output=True, text=True)
    probe.unlink()
    text = out.stdout + out.stderr
    if out.returncode:
        raise SystemExit(f"axiom probe failed:\n{text[-2000:]}")
    result = {}
    for n in names:
        m = re.search(rf"'{re.escape(n)}' (does not depend on any axioms|depends on axioms: \[(.*?)\])", text, re.S)
        if not m:
            raise SystemExit(f"no axiom line for {n}")
        result[n] = sorted(a.strip() for a in (m.group(2) or "").split(",") if a.strip())
    return result


def main() -> None:
    global DEP
    cfg = json.loads(Path(sys.argv[1]).read_text())
    if cfg.get("classic_scope") == "full":
        DEP = FULL_DEP
    src, slug, name = cfg["source"], cfg["slug"], cfg["export_name"]
    rows = [r for r in csv.DictReader((DEP / "declaration_inventory.csv").open()) if r["source_file"] == src]
    decls = [r["declaration_name"] for r in rows]
    ns = lean_ns(src)
    full = [f"{ns}.{d}" for d in decls]
    comp = set(cfg.get("computational", []))
    assert comp <= set(decls), comp - set(decls)
    theorems = [f"{ns}.{d}" for d in decls if d not in comp]
    iface = cfg.get("interface_theorems", [])
    edges = json.loads((DEP / "file_dag.json").read_text())["edges"]
    dependencies = sorted({e["dependency_file"] for e in edges if e["dependent_file"] == src})
    stem = name  # file-name stem of the generated fixtures

    # closure list
    (V / "tooling/classic/closures").mkdir(parents=True, exist_ok=True)
    (V / f"tooling/classic/closures/{slug}.txt").write_text("\n".join(closure(src)) + "\n")

    # export config
    cfgx = {"schema_version": 1, "module": cfg["export_module"],
            "targets": full + iface + cfg.get("extra_targets", []) + cfg.get("extra_statement_only", []),
            # opt-in: auxiliary theorems (e.g. `_proof_N` of an informative definition) exported statement-only too
            "statement_only": theorems + cfg.get("extra_statement_only", []), "body_theorems": iface,
            "definition_targets": [f"{ns}.{d}" for d in decls if d in comp] + cfg.get("extra_targets", []),
            "normalization": cfg.get("normalization", {"theorem_types": [], "subexpression_heads": [],
                                                        "definition_bodies": [], "body_projections": []}),
            "kernel_guard_artifacts": cfg.get("kernel_guard_artifacts", [])}
    (V / f"tooling/classic/{slug}_export_config.json").write_text(json.dumps(cfgx, indent=2) + "\n")

    fx = V / "fixtures/translation_order"
    # fingerprint probe
    q = [r["qualified_name"] for r in rows]
    probe = [f"(* Recomputes the authoritative `Check @name` fingerprints for {src}. *)",
             'Set Warnings "-notation-overridden,-missing-proof-command".', "Set Printing Width 100000.",
             # display context as in the authoritative evidence probe: every module of the closure Require Import-ed
             # (alphabetical order, as classic_reference_evidence.py does for the whole scope)
             *[f"Require Import prosa.{f[:-2].replace('/', '.')}." for f in sorted(closure(src))],
             # display-only: the authoritative evidence was printed with MathComp's notations in scope
             "From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path."]
    probe += cfg.get("probe_extra", [])
    for x in q:
        probe += [f'Goal True. idtac "BEGIN|{x}". Abort.', f"Check @{x}.", f'Goal True. idtac "END|{x}". Abort.']
    (fx / f"{stem}TypeFingerprintProbe.v").write_text("\n".join(probe) + "\n")
    # Lean type audit (the export module imports everything audited)
    la = [f"import {cfg['export_module']}", "set_option pp.fieldNotation false", ""]
    la += [f"#check @{f}" for f in full + iface] + [""] + [f"#print axioms {f}" for f in full + iface]
    (fx / f"{stem}LeanTypeAudit.lean").write_text("\n".join(la) + "\n")
    # imported type audit
    ia = ["From LeanImport Require Import Lean.", f"From FoundationImported Require Import Imported{name}.", ""]
    # the Rocq importer spells non-ASCII identifier characters as `_UU<hex4>_` (rocq-lean-import's clean_string)
    ia += [f"Check Imported{name}.{''.join(c if c.isascii() else f'_UU{ord(c):04x}_' for c in f.replace('.', '_'))}." for f in full]
    (fx / f"{stem}ImportedTypeAudit.v").write_text("\n".join(ia) + "\n")

    certdir = V / "certificates" / slug
    certdir.mkdir(parents=True, exist_ok=True)
    (certdir / f"Imported{name}.v").write_text(f'From LeanImport Require Import Lean.\nLean Import "{name}.out".\n')
    axioms = actual_axioms(cfg["export_module"], full + iface)
    (certdir / f"{slug}_lean_axiom_config.json").write_text(json.dumps(
        {"declarations": {f: {"allowed_axioms": axioms[f]} for f in full + iface}}, indent=2) + "\n")
    principal = cfg.get("principal", {})
    certs = []
    for d in decls:
        certs += principal.get(d, [f"{d.replace('.', '_')}_correspondence"])
    certs += cfg.get("helpers", [])
    imp = f"Imported{name}"
    aconf = {"schema_version": 1,
             "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict", "interpret_strict"],
             "importer_foundation": [f"{imp}.propext", f"{imp}.Quot_sound", f"{imp}.Classical_choice",
                                     "I.propext", "I.Quot_sound", "I.Classical_choice",
                                     "PrimInt63.lsr", "PrimInt63.land", "PrimInt63.int", "PrimInt63.eqb"],
             "rocq_sprop_uip": ["Lean.eq", "Lean.eq_inst1", f"{imp}.True", f"{imp}.HEq", f"{imp}.HEq_inst1",
                                "I.True", "I.HEq", "I.HEq_inst1",
                                "SubadditivityNatCorrespondence.SubNatTrue", "SubNatTrue"]
                               + cfg.get("extra_uip", []),
             "statement_only_dependencies": [],
             "certificates": {c: {"certificate": c, "source_theorem": "", "target_imported_theorem": "",
                                  "semantic_premise_tokens": [f"{stem}SemanticPremise", "OperationBridgePremise"]}
                              for c in certs}}
    for key in ("prop_sprop_foundation", "importer_foundation", "rocq_sprop_uip"):
        if key in cfg:   # allowlist pruned to the names observed by a previous check
            aconf[key] = cfg[key]
    if cfg.get("rocq_functional_extensionality"):   # opt-in, user decision 2026-10-03 (the pipeline enforces the scope)
        aconf["rocq_functional_extensionality"] = list(cfg["rocq_functional_extensionality"])
    for d, r in zip(decls, rows):
        for c in principal.get(d, [f"{d.replace('.', '_')}_correspondence"]):
            aconf["certificates"][c]["source_theorem"] = r["qualified_name"]
            if d not in comp:
                aconf["certificates"][c]["target_imported_theorem"] = f"{ns}.{d}".replace(".", "_")
    (certdir / f"{slug}_assumption_config.json").write_text(json.dumps(aconf, indent=2) + "\n")
    audit = [f"From FoundationCertificates Require Import {cfg['chain'][-1]}.", "Set Printing Width 1000.", ""]
    for c in certs:
        audit += [f'Goal Logic.True. idtac "AUDIT_BEGIN {c}". exact Logic.I. Qed.', f"Print Assumptions {c}.",
                  f'Goal Logic.True. idtac "AUDIT_END {c}". exact Logic.I. Qed.', ""]
    (certdir / f"{stem}AssumptionAudit.v").write_text("\n".join(audit))

    # the accepted v0.6 Rocq 9.3 util patches of the closure's util files (scripts/classic_split_util_patches.py)
    umap = json.loads((V / "patches/classic/util_patch_map.json").read_text())
    patches = cfg.get("patches", []) + [p for f in closure(src) for p in umap.get(f, [])]
    spec = {
        "rank": cfg["rank"], "layer": cfg.get("layer", 0), "tag": cfg["tag"], "slug": slug, "family": "classic",
        **({"classic_scope": "full"} if cfg.get("classic_scope") == "full" else {}),
        "source": src, "dependencies": dependencies, "declaration_count": len(decls),
        "base_run": cfg.get("base_run"), "base_checks": cfg.get("base_checks", []),
        "source_mode": "official_closure",
        **({"rocq_funext_scope": True} if cfg.get("rocq_functional_extensionality") else {}),
        "official_closure": {"files": f"tooling/classic/closures/{slug}.txt", "patches": patches,
                             **({"module_change": cfg["module_change"]} if cfg.get("module_change") else {})},
        "fingerprint_probe": f"Validation/fixtures/translation_order/{stem}TypeFingerprintProbe.v",
        "production": cfg["production"], "production_olean": cfg["production"][:-5] + ".olean",
        "lean_namespace": ns, "fixtures": cfg.get("fixtures", []),
        "lean_type_audit": f"Validation/fixtures/translation_order/{stem}LeanTypeAudit.lean",
        "export_config": f"Validation/tooling/classic/{slug}_export_config.json", "export_name": name,
        "cert_dir": f"certificates/{slug}", "chain": cfg["chain"], "audit_module": f"{stem}AssumptionAudit",
        "imported_type_audit": f"Validation/fixtures/translation_order/{stem}ImportedTypeAudit.v",
        "assumption_config": f"certificates/{slug}/{slug}_assumption_config.json",
        "lean_axiom_config": f"certificates/{slug}/{slug}_lean_axiom_config.json",
        "computational": sorted(comp, key=decls.index), "principal": principal,
        "helpers": cfg.get("helpers", []),
        "previous_status": cfg["previous_status"], **previous_counts(cfg),
        "input_relations": cfg.get("input_relations", []), "coverage_for_inner_binders": [],
        "lean_representation_note": cfg.get("lean_representation_note", ""),
        "extra_pinned_sources": [], "extra_artifacts": [],
        "extra_olean_artifacts": (cfg["extra_olean_artifacts"] if "extra_olean_artifacts" in cfg else
                                  auto_olean_artifacts([cfg["production"][:-5].replace("/", ".")] +
                                                       [f"Validation.fixtures.translation_order.{f}"
                                                        for f in cfg.get("fixtures", [])])),
        **({"export_env": cfg["export_env"]} if cfg.get("export_env") else {}),
        **({"export_diagnosis": cfg["export_diagnosis"]} if cfg.get("export_diagnosis") else {}),
        **({"extra_statement_only": cfg["extra_statement_only"]} if cfg.get("extra_statement_only") else {}),
        **{k: cfg[k] for k in ("own_qualified_in_type", "dependency_qualified_in_type") if cfg.get(k)},
    }
    (V / "tooling/classic/file_specs").mkdir(parents=True, exist_ok=True)
    (V / f"tooling/classic/file_specs/{slug}.json").write_text(json.dumps(spec, indent=2) + "\n")
    print(json.dumps({"declarations": len(decls), "theorems": len(theorems), "dependencies": dependencies,
                      "closure": closure(src), "certificates": certs}, indent=1))


if __name__ == "__main__":
    main()
