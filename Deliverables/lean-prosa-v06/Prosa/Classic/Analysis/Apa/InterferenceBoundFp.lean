-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/apa/interference_bound_fp.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 43)

import Prosa.Util.Sum
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Analysis.Apa.WorkloadBound
import Prosa.Classic.Analysis.Apa.InterferenceBound

/-!
Total interference bound for FP scheduling under APA (Rocq module
`InterferenceBoundFP`, `classic/analysis/apa`).

Representation notes: `\sum_((tsk_other, R_other) <- R_prev | P tsk_other) F`
binds the pair by pattern matching in both the filter and the summand and is
`Prosa.Util.Sum.sumFiltered R_prev (fun (tsk_other, _) => P tsk_other)
(fun (tsk_other, R_other) => F)`; the section-local `Let`s
`total_interference_bound` and `hp_task_in alpha'` (which shadows the section
variable `alpha'`) are unfolded.  The Rocq module re-exports
`InterferenceBoundGeneric`.  Binder lists follow the Rocq contract
(`task_deadline` is not taken).
-/

namespace Prosa.Classic.Analysis.Apa.InterferenceBoundFp.InterferenceBoundFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Priority.Priority (FP_policy)
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference (higher_priority_task_in)
open Prosa.Util.Sum (sumFiltered)

export Prosa.Classic.Analysis.Apa.InterferenceBound.InterferenceBoundGeneric
  (interference_bound_generic)

universe u

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus) (tsk : sporadic_task)
    (alpha' : affinity num_cpus) (R_prev : List (sporadic_task × time)) (delta : time)
    (higher_eq_priority : FP_policy sporadic_task) : Nat :=
  sumFiltered R_prev
    (fun (tsk_other, _R_other) =>
      higher_priority_task_in alpha higher_eq_priority tsk alpha' tsk_other)
    (fun (tsk_other, R_other) =>
      interference_bound_generic task_cost task_period tsk delta (tsk_other, R_other))

end Prosa.Classic.Analysis.Apa.InterferenceBoundFp.InterferenceBoundFP
