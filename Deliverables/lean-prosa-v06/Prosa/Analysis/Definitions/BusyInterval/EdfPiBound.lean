-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/busy_interval/edf_pi_bound.v

import Prosa.Util.Minmax
import Prosa.Util.Epsilon
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Analysis.Definitions.RequestBoundFunction

namespace Prosa.Analysis.Definitions.BusyInterval.EdfPiBound

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Util.Minmax
open Prosa.Util.Sum

/-! Representation notes: `\max_(x <- xs | P x) F x` is the accepted
`bigMaxListCond xs P F`; `\sum_(x <- xs | P x) F x` is the accepted
`sumFiltered xs P F`; `a > b` is `decide (b < a)`; `a <= b` in a Boolean
position is `decide (a ≤ b)`; `ε` is `1`; the section-local `Let D tsk :=
task_deadline tsk` is inlined; the two local `let` functions are kept.
Binder orders follow the elaborated types (the section's `sbf` import
contributes nothing to this definition). -/

section BoundedBusyIntervalUnderEDF

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task]
variable [TaskMaxNonpreemptiveSegment Task] [MaxArrivals Task]

/-- Bound on the length of a busy interval starting with priority inversion
under EDF. -/
def longest_busy_interval_with_pi (ts : List Task) (tsk : Task) : Nat :=
  let lp_interference := fun tsk_lp : Task => task_max_nonpreemptive_segment tsk_lp - ε
  let hep_interference := fun tsk_lp : Task =>
    sumFiltered ts (fun tsk_hp => decide (task_deadline tsk_hp ≤ task_deadline tsk_lp))
      (fun tsk_hp => task_request_bound_function tsk_hp (task_deadline tsk_lp - task_deadline tsk_hp))
  bigMaxListCond ts (fun tsk_lp => decide (task_deadline tsk < task_deadline tsk_lp))
    (fun tsk_lp => lp_interference tsk_lp + hep_interference tsk_lp)

end BoundedBusyIntervalUnderEDF

end Prosa.Analysis.Definitions.BusyInterval.EdfPiBound
