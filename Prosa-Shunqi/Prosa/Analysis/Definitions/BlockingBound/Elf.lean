-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/blocking_bound/elf.v

import Prosa.Util.Minmax
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Task.Arrival.Curves
import Prosa.Model.Priority.Elf

namespace Prosa.Analysis.Definitions.BlockingBound.Elf

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.Minmax

/-! Representation notes: `\max_(x <- xs | P x) F x` is the accepted
`bigMaxListCond xs P F`; the section `Let`s `blocking_relevant`,
`lp_tsk_blocking_relevant` and `ep_tsk_blocking_relevant` are inlined with
the source's Boolean structure; `ε` is `1`; `A%:R` is the cast `(A : Int)`
and `(x < y)%R` on `int` is `decide (x < y)` (as in the accepted
`model/priority/gel.v`). Binder order follows the elaborated type (the
unused section `Job` is absent). -/

/-- ELF blocking bound: the longest nonpreemptive segment (minus one) of a
blocking-relevant task that is lower-priority, or equal-priority with a
later priority point than the job's (relative offset `A`). -/
def blocking_bound {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskMaxNonpreemptiveSegment Task]
    [PriorityPoint Task] (ts : List Task) [MaxArrivals Task] [FP : FP_policy Task]
    (tsk : Task) (A : duration) : Nat :=
  bigMaxListCond ts
    (fun tsk_o =>
      (hp_task (FP := FP) tsk tsk_o && (decide (0 < max_arrivals tsk_o 1) && decide (0 < task_cost tsk_o))) ||
        (ep_task (FP := FP) tsk tsk_o &&
            decide ((A : Int) + task_priority_point tsk < task_priority_point tsk_o) &&
          (decide (0 < max_arrivals tsk_o 1) && decide (0 < task_cost tsk_o))))
    (fun tsk_o => task_max_nonpreemptive_segment tsk_o - 1)

end Prosa.Analysis.Definitions.BlockingBound.Elf
