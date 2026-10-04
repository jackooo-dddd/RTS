-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/blocking_bound/edf.v

import Prosa.Util.Minmax
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Task.Arrival.Curves

namespace Prosa.Analysis.Definitions.BlockingBound.Edf

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.Minmax

/-! Representation notes: `\max_(x <- xs | P x) F x` is the accepted
`bigMaxListCond xs P F` (MathComp's right fold with `maxn` and identity `0`);
`a > b` is `decide (b < a)`; `ε` is `1`; the section-local `Let D tsk :=
task_deadline tsk` is inlined. Binder orders follow the elaborated types. -/

/-- A task is relevant for blocking if it can release a job and has positive cost. -/
def blocking_relevant {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (tsk_o : Task) : Bool :=
  decide (0 < max_arrivals tsk_o 1) && decide (0 < task_cost tsk_o)

/-- EDF blocking bound: the longest nonpreemptive segment (minus one) of a
blocking-relevant task with a later relative deadline. -/
def blocking_bound {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task]
    [TaskMaxNonpreemptiveSegment Task] (ts : List Task) [MaxArrivals Task]
    (tsk : Task) (A : duration) : Nat :=
  bigMaxListCond ts
    (fun tsk_o => blocking_relevant tsk_o &&
      decide (task_deadline tsk + A < task_deadline tsk_o))
    (fun tsk_o => task_max_nonpreemptive_segment tsk_o - 1)

end Prosa.Analysis.Definitions.BlockingBound.Edf
