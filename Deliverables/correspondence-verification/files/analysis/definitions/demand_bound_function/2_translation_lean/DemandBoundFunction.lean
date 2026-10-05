-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/demand_bound_function.v

import Prosa.Analysis.Definitions.RequestBoundFunction

namespace Prosa.Analysis.Definitions.DemandBoundFunction

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Util.Sum

/-! Representation notes: `\sum_(x <- xs) F x` is the accepted `sumSeq xs F`;
the local `let delta'` is kept as a `let`. Binder orders follow the
elaborated types. -/

section DemandBoundFunction

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task]

/-- A task's DBF is its RBF shifted by `task_deadline tsk - 1` time units. -/
def task_demand_bound_function (tsk : Task) (delta : duration) : Nat :=
  let delta' := delta - (task_deadline tsk - 1)
  task_request_bound_function tsk delta'

/-- The total DBF of a task set. -/
def total_demand_bound_function (ts : List Task) (delta : duration) : Nat :=
  sumSeq ts (fun tsk => task_demand_bound_function tsk delta)

end DemandBoundFunction

end Prosa.Analysis.Definitions.DemandBoundFunction
