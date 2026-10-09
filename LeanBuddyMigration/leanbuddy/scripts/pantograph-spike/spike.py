#!/usr/bin/env python3
"""Phase 1 spike: the six checks of BACKEND_DECISION.md *First spike*, against the built Lean package.

usage: python3 spike.py --project <built lean-prosa-v06 copy> --repl <Pantograph .lake/build/bin/repl> [--out results.json]

Every check prints PASS/FAIL with the evidence; results are also written as JSON. Nothing is written into the
project directory.
"""
import argparse
import json
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from pantograph import Pantograph, split_header  # noqa: E402

TASK = {
    "solution_file": "CaseStudies/ECRTS2005/Lemma3/Solution.lean",
    "statement": "CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF.Lemma3_05_statement",
    "levels": ["u", "v"],
}

INTROS = ("intro sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline "
          "job_task arr_seq")


def regions_body(base_body, region_a, region_b, tail="sorry"):
    """Replace the `solution` proof of the benchmark file by: unfold, intros, two delegated regions, tail."""
    head = base_body.split(":= by", 1)[0] + ":= by\n"
    end = "\n\nend " + base_body.rsplit("end ", 1)[1]
    return (head
            + f"  unfold {TASK['statement'].rsplit('.', 1)[1]}\n"
            + f"  {INTROS}\n"
            + "  -- proof_region begin admit_id: A\n"
            + f"  have hA : ∀ j : Job, job_cost j = job_cost j := (by\n    {region_a}\n  )\n"
            + "  -- proof_region end\n"
            + "  -- proof_region begin admit_id: B\n"
            + f"  have hB : ∀ j : Job, job_arrival j + 0 = job_arrival j := (by\n    {region_b}\n  )\n"
            + "  -- proof_region end\n"
            + f"  {tail}"
            + end)


def goals_of(reply):
    out = []
    for t in reply.get("targets", []):
        for g in t["goals"]:
            out.append({"state": t["stateId"], "target": g["target"]["pp"],
                        "vars": [v["userName"] for v in g["vars"]]})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", required=True)
    ap.add_argument("--repl", required=True)
    ap.add_argument("--out", default="spike-results.json")
    args = ap.parse_args()
    project = Path(args.project)
    res = {}

    def report(name, ok, evidence):
        res[name] = {"pass": ok, "evidence": evidence}
        print(f"[{'PASS' if ok else 'FAIL'}] {name}: {json.dumps(evidence, ensure_ascii=False)[:600]}")

    source = (project / TASK["solution_file"]).read_text()
    modules, header, body = split_header(source)
    print("imports:", modules)
    pg = Pantograph(args.repl, project, modules)
    print(f"startup {pg.startup_seconds:.1f}s, rss {pg.rss_mb():.0f} MB")
    res["startup"] = {"seconds": round(pg.startup_seconds, 1), "rss_mb": round(pg.rss_mb() or 0)}

    # 1. Goal order ------------------------------------------------------------------------------------------
    two = regions_body(body, "sorry", "sorry")
    t0 = time.time()
    r = pg.send("frontend.distil", {"file": two, "ignoreValues": False})
    gs = goals_of(r)
    targets = [g["target"] for g in gs]
    ia = next((i for i, t in enumerate(targets) if "job_cost j = job_cost j" in t), None)
    ib = next((i for i, t in enumerate(targets) if "job_arrival j + 0" in t), None)
    report("1_goal_order", ia is not None and ib is not None,
           {"seconds": round(time.time() - t0, 1), "order": targets, "A_index": ia, "B_index": ib,
            "source_order_is_A_then_B": True, "returned_reversed": (ib is not None and ia is not None and ib < ia),
            "error": r.get("desc")})

    # 2. Header ----------------------------------------------------------------------------------------------
    with_header = header + "\n" + two
    r_hdr = pg.send("frontend.distil", {"file": with_header, "ignoreValues": False})
    # a package module the task does not import (Prosa v0.6 readiness facts)
    new_mod, new_decl = "Prosa.Analysis.Facts.Readiness.Basic", "Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_compliance"
    uses_new_import = two.replace("  sorry\n\nend", f"  have _x := @{new_decl}\n  sorry\n\nend")
    r_noimp = pg.send("frontend.distil", {"file": uses_new_import, "ignoreValues": False})
    pg.close()
    pg = Pantograph(args.repl, project, modules + [new_mod])
    r_imp = pg.send("frontend.distil", {"file": uses_new_import, "ignoreValues": False})
    report("2_header", "error" in r_hdr and "import" in r_hdr.get("desc", "") and "error" in r_noimp and "targets" in r_imp,
           {"with_import_lines": r_hdr.get("desc", "")[:200],
            "new_decl_before_restart": (r_noimp.get("desc") or "ok")[:200],
            "new_decl_after_restart_with_import": "ok" if "targets" in r_imp else r_imp.get("desc", "")[:200]})

    # 3. Broken region ---------------------------------------------------------------------------------------
    broken = regions_body(body, "exact Nat.does_not_exist", "sorry")
    r_broken = pg.send("frontend.distil", {"file": broken, "ignoreValues": False})
    masked = regions_body(body, "sorry", "sorry")
    r_masked = pg.send("frontend.distil", {"file": masked, "ignoreValues": False})
    report("3_broken_region", "error" in r_broken and len(goals_of(r_masked)) >= 2,
           {"broken": (r_broken.get("desc") or f"{len(goals_of(r_broken))} goals")[:200],
            "masked_goals": len(goals_of(r_masked))})

    # 4. Root goal -------------------------------------------------------------------------------------------
    st = pg.send("goal.start", {"expr": TASK["statement"] + ".{u, v}", "levels": TASK["levels"]})
    sid = st.get("stateId")
    unf = pg.send("goal.tactic", {"stateId": sid, "goalId": 0, "tactic": f"unfold {TASK['statement']}"})
    unfolded = unf["goals"][0]["target"]["pp"] if "goals" in unf else None
    show_ok = pg.send("goal.tactic", {"stateId": sid, "tactic": f"show {unfolded}"}) if unfolded else {}
    type0 = unfolded.replace("Type u", "Type 0", 1) if unfolded else ""
    show_t0 = pg.send("goal.tactic", {"stateId": sid, "tactic": f"show {type0}"}) if unfolded else {}
    swapped = unfolded.replace("job_cost job_deadline", "job_deadline job_cost", 1) if unfolded else ""
    report("4_root_goal", "goals" in show_ok and "goals" not in show_t0,
           {"start": st.get("error") or "ok", "unfolded_len": len(unfolded or ""),
            "unfolded_head": (unfolded or "")[:300],
            "show_unfolded_pp": "ok" if "goals" in show_ok else (show_ok.get("messages") or show_ok)[:1],
            "show_Type0": "ok" if "goals" in show_t0 else "rejected", "Type0_differs": type0 != unfolded})

    # 5. Holes -----------------------------------------------------------------------------------------------
    sh = pg.send("goal.tactic", {"stateId": sid, "tactic": "show _"})
    sx = pg.send("goal.tactic", {"stateId": sid, "tactic": "show ?x"})
    echo_hole = pg.send("expr.echo", {"expr": "_", "type": "Prop"})
    echo_app = pg.send("expr.echo", {"expr": "(1 : Nat) = _", "type": "Prop"})
    probe = pg.send("goal.tactic", {"stateId": sid, "tactic": "have _probe : (_ = (1 : Nat)) := sorry"})
    report("5_holes", "goals" in sh and "goals" in sx and "error" in echo_hole and "error" in echo_app,
           {"show_": "accepted" if "goals" in sh else "rejected", "show_?x": "accepted" if "goals" in sx else "rejected",
            "echo_hole": echo_hole.get("desc", "ok")[:160], "echo_app_hole": echo_app.get("desc", "ok")[:160],
            "have_probe": "accepted" if "goals" in probe else (probe.get("messages") or [{}])[0].get("data", "")[:160]})

    # 6. Limits ----------------------------------------------------------------------------------------------
    slow = pg.send("goal.start", {"expr": "(List.range 20000).foldl (· + ·) 0 = 199990000"})
    pg.send("options.set", {"timeout": 2000})
    t0 = time.time()
    r_to = pg.send("goal.tactic", {"stateId": slow["stateId"], "tactic": "decide"}, timeout=120)
    t_to = time.time() - t0
    t0 = time.time()
    r_hb = pg.send("goal.tactic", {"stateId": slow["stateId"], "tactic": "set_option maxHeartbeats 2000 in decide"},
                   timeout=120)
    t_hb = time.time() - t0
    rss_task = pg.rss_mb()
    pg.close()
    pg_full = Pantograph(args.repl, project, ["Mathlib", "Prosa"])
    rss_full = pg_full.rss_mb()
    full_start = pg_full.startup_seconds
    pg_full.close()

    def msg(r):
        if "error" in r:
            return r["error"] + ": " + r.get("desc", "")[:160]
        m = r.get("messages") or []
        return ("goals" in r and "solved/ok") or (m[0]["data"][:160] if m else "no message")

    report("6_limits", t_to < 60 and t_hb < 60,
           {"timeout_2000ms_decide": {"seconds": round(t_to, 1), "reply": msg(r_to)},
            "maxHeartbeats_2000_decide": {"seconds": round(t_hb, 1), "reply": msg(r_hb)},
            "rss_mb_task_imports": round(rss_task or 0), "rss_mb_Mathlib_and_Prosa": round(rss_full or 0),
            "startup_seconds_Mathlib_and_Prosa": round(full_start, 1)})

    Path(args.out).write_text(json.dumps(res, indent=1, ensure_ascii=False))
    print("results:", args.out)


if __name__ == "__main__":
    main()
