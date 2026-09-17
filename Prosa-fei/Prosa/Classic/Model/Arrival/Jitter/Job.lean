-- Translated from: ../rt-proofs/classic/model/arrival/jitter/job.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Job

namespace Prosa.Classic.Model.Arrival.Jitter.Job

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job

section ValidSporadicTaskJobWithJitter

variable {sporadic_task : Type _}
variable (task_cost : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable {Job : Type _}
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → sporadic_task)

variable (j : Job)

def job_jitter_leq_task_jitter : Prop :=
  job_jitter j ≤ task_jitter (job_task j)

def valid_sporadic_job_with_jitter : Prop :=
  valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j ∧
  job_jitter_leq_task_jitter task_jitter job_jitter job_task j

end ValidSporadicTaskJobWithJitter

end Prosa.Classic.Model.Arrival.Jitter.Job
