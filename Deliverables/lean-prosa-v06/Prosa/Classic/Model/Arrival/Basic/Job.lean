-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/basic/job.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 24)

import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence

/-!
Properties of jobs (Rocq module `Job`).  Binder lists follow the Rocq contract,
including interleaved implicit carriers, e.g.
`valid_sporadic_job {sporadic_task} task_cost task_deadline {Job} job_cost job_deadline job_task j`.
Boolean comparisons are `Bool`; equalities and conjunctions are `Prop`.
-/


/- The Rocq module path is mirrored exactly, which repeats a namespace segment
(file `X` containing Rocq `Module X`); this is intentional. -/
set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Arrival.Basic.Job.Job

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence

universe u v

def job_cost_positive {Job : Type u} [DecidableEq Job] (job_cost : Job → time) (j : Job) :
    Bool :=
  decide (0 < job_cost j)

def job_deadline_positive {Job : Type u} [DecidableEq Job] (job_deadline : Job → time)
    (j : Job) : Bool :=
  decide (0 < job_deadline j)

def job_cost_le_deadline {Job : Type u} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (j : Job) : Bool :=
  decide (job_cost j ≤ job_deadline j)

def valid_realtime_job {Job : Type u} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (j : Job) : Prop :=
  job_cost_positive job_cost j = true ∧
  job_cost_le_deadline job_cost job_deadline j = true ∧
  job_deadline_positive job_deadline j = true

def job_cost_le_task_cost {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → sporadic_task) (j : Job) : Bool :=
  decide (job_cost j ≤ task_cost (job_task j))

def job_deadline_eq_task_deadline {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_deadline : Job → time) (job_task : Job → sporadic_task) (j : Job) : Prop :=
  job_deadline j = task_deadline (job_task j)

def valid_sporadic_job {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (j : Job) : Prop :=
  valid_realtime_job job_cost job_deadline j ∧
  job_cost_le_task_cost task_cost job_cost job_task j = true ∧
  job_deadline_eq_task_deadline task_deadline job_deadline job_task j

def cost_of_jobs_from_arrival_sequence_le_task_cost {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true

end Prosa.Classic.Model.Arrival.Basic.Job.Job
