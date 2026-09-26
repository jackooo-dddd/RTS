#!/usr/bin/env python3
"""Generate the validation artifacts for one simple priority-policy file
(model/priority/{deadline_monotonic,edf,fifo,numeric_fixed_priority,
rate_monotonic}.v): a policy instance defined by a `<=`/`>=` comparison of a
Nat-valued class field, plus reflexive/transitive/total lemmas.

Everything generated is ordinary validation input for translation_file_pipeline.py:
fingerprint probe, Lean/imported type audits, export config, the accepted
priority certificate chain re-bound to this artifact, the correspondence
certificate, assumption/axiom configs and the file spec.

Usage: gen_priority_policy_validation.py <policy-key>
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

V = Path(__file__).resolve().parents[1]
FIX = V / "fixtures/translation_order"

# key -> description of the policy file
POLICIES = {
    "dm": dict(src="model/priority/deadline_monotonic.v", mod="DeadlineMonotonic", rank=113,
               kind="FP", insts=[("DM", "le", "_is_")], param=("TaskDeadline", "task_deadline",
               "prosa.model.task.concept", "Prosa.Model.Task.Concept", "Prosa_Model_Task_Concept")),
    "edf": dict(src="model/priority/edf.v", mod="Edf", rank=114,
                kind="JLFP", insts=[("EDF", "le", "_is_")], param=("JobDeadline", "job_deadline",
                "prosa.behavior.job", "Prosa.Behavior.Job", "Prosa_Behavior_Job")),
    "fifo": dict(src="model/priority/fifo.v", mod="Fifo", rank=115,
                 kind="JLFP", insts=[("FIFO", "le", "_is_")], param=("JobArrival", "job_arrival",
                 "prosa.behavior.job", "Prosa.Behavior.Job", "Prosa_Behavior_Job")),
    "nfp": dict(src="model/priority/numeric_fixed_priority.v", mod="NumericFixedPriority", rank=117,
                kind="FP", insts=[("NumericFPAscending", "ge", "NFPA_is_"),
                                  ("NumericFPDescending", "le", "NFPD_is_")],
                param=("TaskPriority", "task_priority", "prosa.model.priority.numeric_fixed_priority",
                       "Prosa.Model.Priority.NumericFixedPriority",
                       "Prosa_Model_Priority_NumericFixedPriority"),
                param_in_file=True, local_instances=True),
    "rm": dict(src="model/priority/rate_monotonic.v", mod="RateMonotonic", rank=118,
               kind="FP", insts=[("RM", "le", "_is_")], param=("SporadicModel", "task_min_inter_arrival_time",
               "prosa.model.task.arrival.sporadic", "Prosa.Model.Task.Arrival.Sporadic",
               "Prosa_Model_Task_Arrival_Sporadic")),
}


def main() -> None:
    key = sys.argv[1]
    p = POLICIES[key]
    src = p["src"]
    base = Path(src).stem
    slug = "model_priority_" + base
    lean_ns = "Prosa.Model.Priority." + p["mod"]
    imp_prefix = lean_ns.replace(".", "_")
    export_name = "Priority" + p["mod"]
    rocq_mod = "prosa." + src[:-2].replace("/", ".")
    cls, field, cls_rocq_mod, cls_lean_ns, cls_imp = p["param"]
    carrier = "Task" if p["kind"] == "FP" else "Job"
    dec = "dT" if carrier == "Task" else "dJ"
    rel = "PdFPRel" if p["kind"] == "FP" else "PdJLFPRel"
    prio = "task" if p["kind"] == "FP" else "job"
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        names = [r["declaration_name"] for r in csv.DictReader(stream) if r["source_file"] == src]
    lemma_names = [n for n in names if n.endswith(("_reflexive", "_transitive", "_total"))]
    class_names = [n for n in names if n == cls]
    inst_names = [n for n in names if n not in lemma_names and n not in class_names]

    # fingerprint probe
    lines = ['(* Recomputes the authoritative `Check @name` fingerprints for ' + src + '. *)',
             'Set Warnings "-notation-overridden,-missing-proof-command".',
             'Set Printing Width 100000.', f'Require Import {rocq_mod}.']
    if p.get("param_in_file"):
        lines += ["(* display-only: a second `TaskPriority` in scope (as in the authoritative",
                  "   all-modules probe, where implementation/definitions/task.v defines one),",
                  "   so the class prints qualified as in the evidence *)",
                  "Module DisplayOnly. Definition TaskPriority := tt. End DisplayOnly. Import DisplayOnly."]
    for n in names:
        q = f"{rocq_mod}.{n}"
        lines += [f'Goal True. idtac "BEGIN|{q}". Abort.', f"Check @{q}.", f'Goal True. idtac "END|{q}". Abort.']
    (FIX / f"{export_name}TypeFingerprintProbe.v").write_text("\n".join(lines) + "\n")
    (FIX / f"{export_name}LeanTypeAudit.lean").write_text(
        f"import {lean_ns}\nset_option pp.fieldNotation false\n\n"
        + "".join(f"#check @{lean_ns}.{n}\n" for n in names) + "\n"
        + "".join(f"#print axioms {lean_ns}.{n}\n" for n in names))
    (FIX / f"{export_name}ImportedTypeAudit.v").write_text(
        f"From LeanImport Require Import Lean.\nFrom FoundationImported Require Import Imported{export_name}.\n\n"
        + "".join(f"Check Imported{export_name}.{imp_prefix}_{n}.\n" for n in names))

    # export config
    cfg = json.loads((V / "tooling/model_priority_coercion_export_config.json").read_text())
    cfg["module"] = lean_ns
    helper_insts = [i for i, _, _ in p["insts"]] if p.get("local_instances") else []
    own = [f"{lean_ns}.{n}" for n in names]
    extra = [f"{lean_ns}.{i}" for i in helper_insts]
    cls_targets = [f"{cls_lean_ns}.{cls}", f"{cls_lean_ns}.{cls}.mk", f"{cls_lean_ns}.{cls}.{field}"]
    cfg["targets"] = own + extra + [t for t in cls_targets if t not in own] + cfg["targets"]
    cfg["statement_only"] = [f"{lean_ns}.{n}" for n in lemma_names]
    cfg["definition_targets"] = [f"{lean_ns}.{n}" for n in inst_names + class_names] + extra + cfg["definition_targets"]
    (V / f"tooling/{slug}_export_config.json").write_text(json.dumps(cfg, indent=2) + "\n")

    # certificates
    cdir = V / f"certificates/{slug}"
    cdir.mkdir(parents=True, exist_ok=True)
    chain = ["PcoBaseAdapter", "PcoStaticOrder", "PcoDynamicOrder", "PriorityCoercionCorrespondence"]
    for m in chain:
        text = (V / f"certificates/model_priority_coercion/{m}.v").read_text()
        (cdir / f"{m}.v").write_text(text.replace("ImportedPriorityCoercion", f"Imported{export_name}"))
    (cdir / f"Imported{export_name}.v").write_text(
        f'From LeanImport Require Import Lean.\nLean Import "{export_name}.out".\n')
    cmod = f"{export_name}Correspondence"
    R = f"{cls_rocq_mod}.{field}"
    L = f"I.{cls_imp}_{cls}_{field}"
    Lmk = f"I.{cls_imp}_{cls}_mk"
    Lty = f"I.{cls_imp}_{cls}"
    body = [
        "From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.",
        f"From prosa Require Import {src[:-2].replace('/', '.')}.",
        "From LeanImport Require Import Lean.",
        f"From FoundationImported Require Import Imported{export_name}.",
        "From FoundationCertificates Require Import PropSPropFoundation LogicalRelation",
        "  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder",
        "  PriorityCoercionCorrespondence.", "",
        f"Module I := Imported{export_name}.", "",
        f"(** Certificates for [{src}]: the parameter class ([{cls}]) is related",
        "    pointwise on Nat with two-way totals; the policy instance(s) are related",
        f"    as [{rel}] for related parameters; the reflexive/transitive/total",
        "    statements: source side is the exact elaborated type of the pinned source",
        "    lemma (via [type of], the source proof is not used), target side the type",
        "    of the imported Lean theorem, related through the accepted",
        "    [pd_*_priorities_certificate]s. *)", "",
        "Ltac type_of_term t := let T := type of t in exact T.", "",
    ]
    if any(cmp == "ge" for _, cmp, _ in p["insts"]):
        body += [
        "Lemma pp_decide_ge_related aR aL bR bL :",
        "  SubNatRel aR aL -> SubNatRel bR bL ->",
        "  PdBoolRel (aR >= bR) (I.Decidable_decide (I.GE_ge_inst1 Lean.Nat I.instLENat aL bL)",
        "    (I.Nat_decLe bL aL)).",
        "Proof. intros Ha Hb. exact (pd_decide_le_related _ _ _ _ Hb Ha). Qed.", "",
    ]
    body += [
        f"Section Policy.",
        f"  Context ({carrier} : eqType).",
        f"  Let {dec} := pd_decidable_eq {carrier}.",
    ]
    param_carrier = "Task" if cls in ("TaskDeadline", "TaskPriority", "SporadicModel") else "Job"
    pdec = "dT" if param_carrier == "Task" else "dJ"
    if param_carrier != carrier:
        raise SystemExit("parameter carrier differs from policy carrier")
    body += [
        f"  Definition PpParamRel (cR : {cls_rocq_mod}.{cls} {carrier}) ({'cL'} : {Lty} {carrier} {dec}) : SProp :=",
        f"    forall x : {carrier}, SubNatRel (@{R} {carrier} cR x) ({L} {carrier} {dec} cL x).",
        f"  Lemma {cls}_source_total cR : PpParamRel cR ({Lmk} {carrier} {dec} (fun x => sub_nat_to_imported (@{R} {carrier} cR x))).",
        "  Proof. intro x. exact (sub_nat_rel_canonical _). Qed.",
        f"  Lemma {cls}_target_total cL : PpParamRel (fun x => sub_nat_to_rocq ({L} {carrier} {dec} cL x)) cL.",
        "  Proof. intro x. exact (sub_nat_rel_surjective _). Qed.", "",
        f"  Variable cR : {cls_rocq_mod}.{cls} {carrier}.",
        f"  Variable cL : {Lty} {carrier} {dec}.",
        "  Hypothesis Hc : PpParamRel cR cL.", "",
    ]
    certs: dict[str, list[str]] = {}
    helpers: list[str] = []
    for inst, cmp, lprefix in p["insts"]:
        inst_cert = f"{inst}_correspondence"
        lemma = "pd_decide_le_related" if cmp == "le" else "pp_decide_ge_related"
        body += [
            f"  Theorem {inst_cert} :",
            f"    {rel} {carrier} (@{rocq_mod}.{inst} {carrier} cR) (I.{imp_prefix}_{inst} {carrier} {dec} cL).",
            f"  Proof. intros x y. exact ({lemma} _ _ _ _ (Hc x) (Hc y)). Qed.", ""]
        if inst in names:
            certs[inst] = [inst_cert]
        else:
            helpers.append(inst_cert)
        prefix = inst + lprefix if lprefix == "_is_" else lprefix
        for prop in ("reflexive", "transitive", "total"):
            n = f"{prefix}{prop}"
            body += [
                f"  Definition src_{n} : Prop := ltac:(type_of_term (@{rocq_mod}.{n} {carrier} cR)).",
                f"  Definition tgt_{n} : SProp := ltac:(type_of_term (@I.{imp_prefix}_{n} {carrier} {dec} cL)).",
                f"  Theorem {n}_correspondence : PropSPropRel src_{n} tgt_{n}.",
                f"  Proof. exact (pd_{prop}_{prio}_priorities_certificate {carrier} _ _ {inst_cert}). Qed.", ""]
            certs[n] = [f"{n}_correspondence"]
    body += ["End Policy.", ""]
    if class_names:
        certs[cls] = [f"{cls}_source_total", f"{cls}_target_total"]
    else:
        helpers += [f"{cls}_source_total", f"{cls}_target_total"]
    (cdir / f"{cmod}.v").write_text("\n".join(body))
    audit = [f"From FoundationCertificates Require Import", "  " + " ".join(chain), f"  {cmod}."]
    for c in [c for cs in certs.values() for c in cs] + helpers:
        audit += ["", f'Goal Logic.True. idtac "AUDIT_BEGIN {c}". exact Logic.I. Qed.',
                  f"Print Assumptions {c}.", f'Goal Logic.True. idtac "AUDIT_END {c}". exact Logic.I. Qed.']
    (cdir / f"{export_name}AssumptionAudit.v").write_text("\n".join(audit) + "\n")
    acfg = json.loads((V / "certificates/model_priority_coercion/priority_coercion_assumption_config.json").read_text())
    for k in ("importer_foundation", "rocq_sprop_uip"):
        acfg[k] = [x.replace("ImportedPriorityCoercion", f"Imported{export_name}") for x in acfg[k]]
    tok = [f"{export_name}SemanticPremise", "OperationBridgePremise"]
    acfg["certificates"] = {}
    for n, cs in certs.items():
        for c in cs:
            acfg["certificates"][c] = dict(certificate=c, source_theorem=f"{rocq_mod}.{n}",
                                           target_imported_theorem=f"{imp_prefix}_{n}", semantic_premise_tokens=tok)
    for c in helpers:
        acfg["certificates"][c] = dict(certificate=c, source_theorem="", target_imported_theorem="",
                                       semantic_premise_tokens=tok)
    (cdir / f"{slug}_assumption_config.json").write_text(json.dumps(acfg, indent=2) + "\n")
    (cdir / f"{slug}_lean_axiom_config.json").write_text(json.dumps(
        {"declarations": {f"{lean_ns}.{n}": {"allowed_axioms": ["propext"] if n.endswith("_total") else []}
                          for n in names}}, indent=2) + "\n")

    spec = {
        "rank": p["rank"], "layer": 14, "tag": "PP" + key.upper(), "slug": slug, "source": src,
        "dependencies": sorted(p.get("deps", ["model/priority/classes.v"])),
        "declaration_count": len(names),
        "base_run": "model_priority_classes_final",
        "base_checks": [
            {"manifest": "model_priority_classes", "olean": "Prosa/Model/Priority/Classes.olean",
             "vo": "model/priority/classes.vo", "vo_key": "official_source_vo_sha256"},
            {"manifest": "model_priority_coercion", "olean": "Prosa/Model/Priority/Coercion.olean",
             "vo": "model/priority/coercion.vo"},
            {"manifest": "model_priority_definitions", "olean": "Prosa/Model/Priority/Definitions.olean"}],
        "source_mode": "pinned",
        "fingerprint_probe": f"Validation/fixtures/translation_order/{export_name}TypeFingerprintProbe.v",
        "production": f"Prosa/Model/Priority/{p['mod']}.lean",
        "production_olean": f"Prosa/Model/Priority/{p['mod']}.olean",
        "lean_namespace": lean_ns, "fixtures": [],
        "lean_type_audit": f"Validation/fixtures/translation_order/{export_name}LeanTypeAudit.lean",
        "export_config": f"Validation/tooling/{slug}_export_config.json", "export_name": export_name,
        "cert_dir": f"certificates/{slug}", "chain": chain + [cmod],
        "audit_module": f"{export_name}AssumptionAudit",
        "imported_type_audit": f"Validation/fixtures/translation_order/{export_name}ImportedTypeAudit.v",
        "assumption_config": f"certificates/{slug}/{slug}_assumption_config.json",
        "lean_axiom_config": f"certificates/{slug}/{slug}_lean_axiom_config.json",
        "computational": inst_names + class_names,
        "principal": {n: cs for n, cs in certs.items() if cs != [f"{n}_correspondence"]},
        "helpers": helpers,
        "previous_status": "TBD", "previous_files": 0, "previous_decls": 0,
        "input_relations": [f"{cls} field related pointwise on Nat (two-way totals)"],
        "coverage_for_inner_binders": [],
        "lean_representation_note": ("the policy instance compares the Nat-valued class field with "
                                     "`decide (_ ≤ _)` / `decide (_ ≥ _)`; local source instances are named "
                                     "`@[instance_reducible]` defs" if p.get("local_instances") else
                                     "the policy instance compares the Nat-valued class field with `decide (_ ≤ _)`"),
    }
    spec_path = V / f"tooling/file_specs/{slug}.json"
    if spec_path.exists():
        old = json.loads(spec_path.read_text())
        spec.update({k: old[k] for k in ("previous_status", "previous_files", "previous_decls")})
    spec_path.write_text(json.dumps(spec, indent=2) + "\n")
    print(slug, names, helpers)


if __name__ == "__main__":
    main()
