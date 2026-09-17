-- Translated from: ../rt-proofs/analysis/facts/model/sequential.v
import Prosa.Model.Task.Sequentiality

namespace Prosa.Analysis.Facts.Model.Sequential

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality

section ExecutionOrder

variable {Job : JobType}
variable {Task : TaskType}
variable [DecidableEq Task]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)

theorem scheduler_executes_job_with_earliest_arrival
    (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched) :
    ∀ (j1 j2 : Job) (t : instant),
      same_task (Task := Task) j1 j2 →
      ¬ completed_by (Job := Job) sched j2 t →
      scheduled_at (Job := Job) sched j1 t →
      job_arrival j1 ≤ job_arrival j2 := by
  intro j1 j2 t TSK NCOMPL SCHED
  by_contra ARR
  push_neg at ARR
  have TSK' : same_task (Task := Task) j2 j1 = true := by
    unfold same_task at TSK ⊢
    rw [BEq.comm]
    exact TSK
  have SEQ := H_sequential_tasks j2 j1 t TSK' ARR SCHED
  exact NCOMPL SEQ

end ExecutionOrder

end Prosa.Analysis.Facts.Model.Sequential
