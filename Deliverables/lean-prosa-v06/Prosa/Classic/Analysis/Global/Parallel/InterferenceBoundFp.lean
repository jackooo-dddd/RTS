-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/parallel/interference_bound_fp.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 128)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Analysis.Global.Parallel.WorkloadBound
import Prosa.Classic.Analysis.Global.Parallel.InterferenceBound
import Prosa.Util.Sum

/-!
FP interference bound for parallel jobs (Rocq module `InterferenceBoundFP` of
`classic/analysis/global/parallel/interference_bound_fp.v`, which `Export`s `InterferenceBoundGeneric`).

Representation notes: `\sum_((tsk_other, R_other) <- R_prev) F` is `sumSeq R_prev (fun (tsk_other, R_other) => F)`
(the v0.6 sequence sum with a pair pattern); the section-local `Let`s (`task_with_response_time`,
`total_interference_bound`) are unfolded. Binder lists follow the Rocq contract (`tsk`, `task_deadline` and
`higher_eq_priority` are not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundFp.InterferenceBoundFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Analysis.Global.Parallel.InterferenceBound.InterferenceBoundGeneric (interference_bound_generic)
open Prosa.Util.Sum (sumSeq)

universe u

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (R_prev : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_generic task_cost task_period delta (tsk_other, R_other))

end Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundFp.InterferenceBoundFP
