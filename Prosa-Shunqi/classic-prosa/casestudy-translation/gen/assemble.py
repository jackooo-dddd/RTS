"""Assemble the Lean translation of a 2009/2014/2015-BOOK case study from the snippet library (one translation per
definition variant, see contracts/variants.json) and the file's hand-written theorem.
usage: assemble.py CASE  (or `all`)"""
import json, sys, importlib
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
VARIANTS = json.load(open(ROOT / "contracts/variants.json"))
MANIFEST = json.load(open(ROOT / "contracts/manifest.json"))

IMPORTS = """import CaseStudies.Common
import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.ConstrainedDeadlines"""

OPENS = """open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq sumFiltered)"""

NOTES = """Representation notes (classic-prosa representation addendum): `minn` is `min`; `x %% p` is `x % p`;
`\\sum_(x <- s) F x` is `sumSeq s F` and `\\sum_(x <- s | P x) F x` is `sumFiltered s P F` (pair patterns are
`fun (a, b) => …`); a Boolean summed as a number is `Bool.toNat`; `sort r s` is `s.mergeSort r` with the
relation decided; `take n s` is `s.take n`; `n.-1` is `n - 1`; `[seq x <- s | P x]` is `s.filter P`;
`x \\notin s` is `!decide (x ∈ s)`; `count P ts` is `ts.val.countP P`; Boolean tests in proposition position
are `= true` (`~~ b` is `(!b) = true`), and chains `a <= t < b` are `(decide (a ≤ t) && decide (t < b)) = true`;
section-local `Let`s are unfolded.  Binder lists follow the Rocq contracts in
`classic-prosa/casestudy-translation/contracts/` (Rocq abstracts exactly the section variables a declaration
uses; a theorem abstracts every variable and hypothesis declared before it, so some binders are unused)."""

def assemble(case):
    mod = importlib.import_module("cases")
    spec = mod.CASES[case]
    snip = {}
    for m in ["snippets_base"] + spec.get("snippet_modules", []):
        snip.update(importlib.import_module(m).S)
    decls = MANIFEST[case]["declarations"]
    body = []
    for d in decls:
        short = d.split(".")[-1]
        if short == spec["theorem_name"]:
            continue
        vid = [v for v, cs in VARIANTS.items() if v.split("#")[0] == short and case in cs]
        assert len(vid) == 1, (case, short, vid)
        assert vid[0] in snip, f"no translation for {vid[0]}"
        body.append(snip[vid[0]])
    thm = spec["theorem"]
    extra_imports = []
    proof = HERE / "proofs" / f"{case}.lean"
    if proof.exists():
        helpers, _, prf = proof.read_text().partition("-- @@PROOF@@\n")
        # a proof may need further (accepted) Lean Prosa modules: its leading `import` lines go to the header
        extra_imports = [l for l in helpers.splitlines() if l.startswith("import ")]
        helpers = "\n".join(l for l in helpers.splitlines() if not l.startswith("import "))
        assert thm.endswith(":= by\n  sorry"), case
        thm = thm[: -len("by\n  sorry")] + prf.rstrip() 
        if helpers.strip():
            body.append(helpers.rstrip())
    body.append(thm)
    ns = spec["namespace"]
    fixes = MANIFEST[case].get("source_fixes", [])
    fixnote = ("\n\nSource repair (the file does not compile in ProsaBuddy's toolchain as written): " + "; ".join(fixes)
               if fixes else "")
    text = f"""-- Case study: RTS_Papers/{MANIFEST[case]['file']}
-- sha256 {MANIFEST[case]['sha256']}
-- (elaborated contract: classic-prosa/casestudy-translation/contracts/{case}.txt)
{IMPORTS}{"".join(chr(10) + l for l in extra_imports)}

/-!
{spec['doc']}{fixnote}

{NOTES}
-/

set_option linter.unusedVariables false

namespace {ns}

{OPENS}

universe u v

""" + "\n\n".join(body) + f"\n\nend {ns}\n"
    out = ROOT / "lean/CaseStudies" / spec["path"]
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    print("wrote", out.relative_to(ROOT))

if __name__ == "__main__":
    mod = importlib.import_module("cases")
    for c in (mod.CASES if sys.argv[1] == "all" else sys.argv[1:]):
        assemble(c)
