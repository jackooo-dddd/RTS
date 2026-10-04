-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/sequential.v

import Prosa.Model.Task.Sequentiality
import Prosa.Analysis.Definitions.Readiness
import Prosa.Analysis.Facts.Model.TaskArrivals

namespace Prosa.Analysis.Facts.Model.Sequential

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Sequentiality
open Prosa.Analysis.Definitions.Readiness
open Prosa.Analysis.Facts.Model.TaskArrivals

/-! Execution order under sequential tasks, and sequential tasks from a
sequential readiness model.
Binders follow the elaborated source types. Representation: a Boolean in
`Prop` position is `= true`; `~~ b` is `(!b) = true`. -/

section ExecutionOrder

variable {Job : JobType} [DecidableEq Job] {Task : TaskType} [DecidableEq Task]

/-- Under sequential tasks, a scheduled job arrived no later than any
incomplete job of its task. -/
theorem scheduler_executes_job_with_earliest_arrival [JobTask Job Task] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) :
    sequential_tasks (Task := Task) arr_seq sched →
    ∀ (j1 j2 : Job) (t : instant),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → same_task (Task := Task) j1 j2 = true →
      (!completed_by sched j2 t) = true → scheduled_at sched j1 t = true →
      job_arrival j1 ≤ job_arrival j2 := by
  intro hseq j1 j2 t h1 h2 htsk hnc hs
  rcases Nat.lt_or_ge (job_arrival j2) (job_arrival j1) with hlt | hge
  · exfalso
    have hc := hseq j2 j1 t h2 h1 (by rw [same_task_sym]; exact htsk) hlt hs
    rw [hc] at hnc
    exact absurd hnc (by decide)
  · exact hge

/-- An earlier-arrived incomplete job and a scheduled job stem from
different tasks. -/
theorem sequential_tasks_different_tasks [JobTask Job Task] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) :
    sequential_tasks (Task := Task) arr_seq sched →
    ∀ (j1 j2 : Job) (t : instant),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_arrival j1 < job_arrival j2 →
      (!completed_by sched j1 t) = true → scheduled_at sched j2 t = true →
      (!same_task (Task := Task) j1 j2) = true := by
  intro hseq j1 j2 t h1 h2 hlt hnc hs
  cases hst : same_task (Task := Task) j1 j2
  · rfl
  · exfalso
    have hc := hseq j1 j2 t h1 h2 hst hlt hs
    rw [hc] at hnc
    exact absurd hnc (by decide)

end ExecutionOrder

section FromSequentialReadiness

variable {Job : JobType} [DecidableEq Job] {Task : TaskType} [DecidableEq Task]

/-- A sequential readiness model yields sequential tasks in every valid
schedule. -/
theorem sequential_tasks_from_readiness [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
    ∀ JR : JobReady Job PState, sequential_readiness JR (Task := Task) arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
      sequential_tasks (Task := Task) arr_seq sched := by
  intro hc JR hseq sched hvs j j' t hin hin' hsame hlt hs'
  have hpjc := hseq sched j' t (hvs.2 j' t hs')
  unfold prior_jobs_complete at hpjc
  rw [List.all_eq_true] at hpjc
  apply hpjc j
  have hmem := job_in_task_arrivals_between arr_seq hc (job_task (Task := Task) j') j 0 (job_arrival j')
    hin (by unfold same_task at hsame; exact of_decide_eq_true hsame)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.zero_le _, hlt⟩)
  unfold task_arrivals_before
  exact of_decide_eq_true hmem

end FromSequentialReadiness

end Prosa.Analysis.Facts.Model.Sequential
