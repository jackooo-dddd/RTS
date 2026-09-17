-- Translated from: ../rt-proofs/classic/model/arrival/basic/job.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace Prosa.Classic.Model.Arrival.Basic.Job

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section ValidJob

variable {Job : Type _} (job_cost : Job → Time) (j : Job)

def job_cost_positive : Prop := job_cost j > 0

end ValidJob

section ValidRealtimeJob

variable {Job : Type _} (job_cost : Job → Time) (job_deadline : Job → Time) (j : Job)

def job_deadline_positive : Prop := job_deadline j > 0

def job_cost_le_deadline : Prop := job_cost j ≤ job_deadline j

def valid_realtime_job : Prop :=
  job_cost_positive job_cost j ∧
  job_cost_le_deadline job_cost job_deadline j ∧
  job_deadline_positive job_deadline j

end ValidRealtimeJob

section ValidSporadicTaskJob

variable {sporadic_task : Type _} (task_cost : sporadic_task → Time) (task_deadline : sporadic_task → Time)
variable {Job : Type _} (job_cost : Job → Time) (job_deadline : Job → Time) (job_task : Job → sporadic_task)
variable (j : Job)

def job_cost_le_task_cost : Prop :=
  job_cost j ≤ task_cost (job_task j)

def job_deadline_eq_task_deadline : Prop :=
  job_deadline j = task_deadline (job_task j)

def valid_sporadic_job : Prop :=
  valid_realtime_job job_cost job_deadline j ∧
  job_cost_le_task_cost task_cost job_cost job_task j ∧
  job_deadline_eq_task_deadline task_deadline job_deadline job_task j

end ValidSporadicTaskJob

section ValidTaskJob

variable {Task : Type _} (task_cost : Task → Time)
variable {Job : Type _} (job_cost : Job → Time) (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)

def cost_of_jobs_from_arrival_sequence_le_task_cost : Prop :=
  ∀ j, arrives_in arr_seq j →
    job_cost_le_task_cost task_cost job_cost job_task j

end ValidTaskJob

end Prosa.Classic.Model.Arrival.Basic.Job
