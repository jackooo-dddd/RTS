-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/jitter/job.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 41)

import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job

/-!
Jobs with jitter (Rocq module `JobWithJitter`, which `Export`s `Job`).

Representation notes: Boolean tests in proposition position are `= true`; the section-local
`Let j_is_valid_job` is unfolded. Binder lists follow the Rocq contract; in this file the section variables
are declared in the order `job_task, job_jitter`.
-/

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.Job.Job

universe u v

def job_jitter_leq_task_jitter {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_task : Job → sporadic_task) (job_jitter : Job → time) (j : Job) : Bool :=
  decide (job_jitter j ≤ task_jitter (job_task j))

def valid_sporadic_job_with_jitter {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time) (j : Job) : Prop :=
  valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j ∧
    job_jitter_leq_task_jitter task_jitter job_task job_jitter j = true

end Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter
