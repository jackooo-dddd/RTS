-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/job_constructor.v

import Prosa.Implementation.Facts.MaximalArrivalSequence
import Prosa.Implementation.Definitions.Task

namespace Prosa.Implementation.Definitions.JobConstructor

open Prosa.Behavior.Time
open Prosa.Implementation.Definitions.Task

/-! Job construction for concrete arrival sequences.

Representation: the source's `concrete_task : eqType` and `concrete_job : eqType` carriers are the concrete
structures (with their derived decidable equalities); `iota 0 n` is `List.range' 0 n`; `map` is `List.map`. -/

/-- The concrete task type. -/
abbrev Task : Type := concrete_task

/-- The concrete job type. -/
abbrev Job : Type := concrete_job

/-- The job of task `tsk` released at `t` with identifier `id`: its cost is the task cost and its deadline is
`t` plus the task deadline. -/
def generate_job_at (tsk : concrete_task) (t : instant) (id : Nat) : Job :=
  { job_id := id
    job_arrival := t
    job_cost := tsk.task_cost
    job_deadline := t + tsk.task_deadline
    job_task := tsk }

/-- The `n` jobs of task `tsk` released at `t`, with identifiers `0, …, n - 1`. -/
def generate_jobs_at (tsk : concrete_task) (n : Nat) (t : instant) : List Job :=
  (List.range' 0 n).map (generate_job_at tsk t)

end Prosa.Implementation.Definitions.JobConstructor
