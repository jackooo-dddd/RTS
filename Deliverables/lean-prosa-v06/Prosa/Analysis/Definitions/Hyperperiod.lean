-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/hyperperiod.v

import Prosa.Model.Task.Arrival.Periodic
import Prosa.Model.Task.Offset
import Prosa.Util.Lcmseq

namespace Prosa.Analysis.Definitions.Hyperperiod

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Offset
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Util.Lcmseq

/-! Hyperperiods of periodic task sets.

Representation: `%/` is `/` on `Nat`; MathComp's `index x s` is `List.idxOf x s` and `nth x0 s n` is
`s.getD n x0`; `map` is `List.map`. The section-local abbreviations `O_max` and `HP` are unfolded to
`max_task_offset ts` and `hyperperiod ts`. -/

section Hyperperiod

variable {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]

/-- The hyperperiod of a task set: the least common multiple of the task periods. -/
def hyperperiod (ts : TaskSet Task) : duration :=
  lcml (ts.map task_period)

end Hyperperiod

section HyperperiodDefinitions

variable {Task : TaskType} [DecidableEq Task] [TaskOffset Task] [PeriodicModel Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
variable (ts : TaskSet Task) (arr_seq : arrival_sequence Job)

/-- The index of the hyperperiod containing `t`; the first hyperperiod starts at the maximum offset. -/
def hyperperiod_index (t : instant) : Nat :=
  (t - max_task_offset ts) / hyperperiod ts

/-- The starting instant of the hyperperiod containing `t`. -/
def starting_instant_of_hyperperiod (t : instant) : Nat :=
  hyperperiod_index ts t * hyperperiod ts + max_task_offset ts

/-- The starting instant of the hyperperiod in which `j` arrives. -/
def starting_instant_of_corresponding_hyperperiod (j : Job) : Nat :=
  starting_instant_of_hyperperiod ts (job_arrival j)

/-- The jobs of `tsk` arriving in the hyperperiod that starts at `h`. -/
def jobs_in_hyperperiod (h : instant) (tsk : Task) : List Job :=
  task_arrivals_between arr_seq tsk h (h + hyperperiod ts)

/-- The index of `j` among the jobs of `tsk` in the hyperperiod starting at `h`. -/
def job_index_in_hyperperiod (j : Job) (h : instant) (tsk : Task) : Nat :=
  (jobs_in_hyperperiod ts arr_seq h tsk).idxOf j

/-- The job of `tsk` in the hyperperiod starting at `h` with the same index as `j` has in its own hyperperiod. -/
def corresponding_job_in_hyperperiod (j : Job) (h : instant) (tsk : Task) : Job :=
  (jobs_in_hyperperiod ts arr_seq h tsk).getD
    (job_index_in_hyperperiod ts arr_seq j (starting_instant_of_corresponding_hyperperiod ts j) tsk) j

end HyperperiodDefinitions

end Prosa.Analysis.Definitions.Hyperperiod
