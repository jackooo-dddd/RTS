-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/interference_bound_fp.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 145)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference
import Prosa.Classic.Analysis.Global.Jitter.WorkloadBound
import Prosa.Classic.Analysis.Global.Jitter.InterferenceBound

/-!
Total interference bound for FP scheduling with release jitter (Rocq module `InterferenceBoundFP` of
`classic/analysis/global/jitter/interference_bound_fp.v`).

Representation notes: `\sum_((tsk_other, R_other) <- R_prev) F` binds the pair by pattern matching and is
`Prosa.Util.Sum.sumSeq R_prev (fun (tsk_other, R_other) => F)`; the section-local `Let`s
(`task_with_response_time`, `total_interference_bound`) are unfolded.  The Rocq module re-exports
`InterferenceBoundJitter`.  Binder lists follow the Rocq contract: `total_interference_bound_fp` does not take the
unused section variables `task_deadline` and `higher_eq_priority`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundFp.InterferenceBoundFP

open Prosa.Classic.Model.Time.Time
open Prosa.Util.Sum (sumSeq)

export Prosa.Classic.Analysis.Global.Jitter.InterferenceBound.InterferenceBoundJitter
  (interference_bound_generic)

universe u

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_jitter : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_generic task_cost task_period task_jitter tsk delta (tsk_other, R_other))

end Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundFp.InterferenceBoundFP
