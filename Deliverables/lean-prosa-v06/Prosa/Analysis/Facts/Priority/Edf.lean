-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/edf.v

import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Model.Task.Sequentiality
import Prosa.Analysis.Facts.Priority.Sequential

namespace Prosa.Analysis.Facts.Priority.Edf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.AlwaysHigherPriority
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Priority.Sequential

/-! Facts about EDF priorities and sequential tasks under EDF.
Binders follow the elaborated source types. The `EDF` policy is the accepted
`EDF` instance, over the job's deadline class in the first fact and over the
accepted task-deadline-derived `job_deadline_from_task_deadline` otherwise,
passed explicitly. Representation: a Boolean equation `b = (x <= y)` is
`b = decide (x ≤ y)`; `same_task j j'` in `Prop` position is `= true`. -/

section PriorityFacts

variable {Job : JobType} [DecidableEq Job]

/-- Under EDF, `hep_job` compares the deadlines. -/
theorem hep_job_deadline [JobDeadline Job] :
    ∀ j j' : Job, (EDF Job).hep_job j j' = decide (job_deadline j ≤ job_deadline j') :=
  fun _ _ => rfl

/-- Under EDF with task-derived deadlines, `hep_job` compares arrival plus
relative deadline. -/
theorem hep_job_task_deadline [JobArrival Job] {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] [JobTask Job Task] :
    ∀ j j' : Job, (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job j j' =
      decide (job_arrival j + task_deadline (job_task (Task := Task) j) ≤
        job_arrival j' + task_deadline (job_task (Task := Task) j')) :=
  fun _ _ => rfl

/-- Under EDF, jobs of the same task are ordered by arrival. -/
theorem hep_job_arrival_edf [JobArrival Job] {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] [JobTask Job Task] :
    ∀ j j' : Job, same_task (Task := Task) j j' = true →
      (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job j j' =
        decide (job_arrival j ≤ job_arrival j') := by
  intro j j' hsame
  unfold same_task at hsame
  rw [hep_job_task_deadline, of_decide_eq_true hsame]
  simp only [Nat.add_le_add_iff_right]

/-- EDF respects the sequential-tasks hypothesis. -/
theorem EDF_respects_sequential_tasks [JobArrival Job] {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] [JobTask Job Task] :
    policy_respects_sequential_tasks (Task := Task)
      (@EDF Job _ (job_deadline_from_task_deadline Job Task)) := by
  intro j j' hsame hle
  rw [hep_job_arrival_edf j j' hsame]
  exact decide_eq_true hle

end PriorityFacts

section SequentialEDF

variable {Job : JobType} [DecidableEq Job]

/-- The EDF policy implies sequential tasks. -/
theorem EDF_implies_sequential_tasks {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState],
      @work_bearing_readiness Job _ _ _ PState _ arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      sequential_tasks (Task := Task) arr_seq sched := by
  intro huni arr_seq hva sched _ hwb hvs _ hvpm hresp j1 j2 t ha1 ha2 hsame hlt hs
  have hsame' : same_task (Task := Task) j2 j1 = true := by rw [same_task_sym]; exact hsame
  exact early_hep_job_is_scheduled arr_seq hva (@EDF Job _ (job_deadline_from_task_deadline Job Task))
    (EDF_is_transitive (Job := Job)) PState huni sched hwb hvs hvpm hresp j1 j2 ha1 hlt
    ((always_higher_priority_jlfp j1 j2).2 (by
      rw [hep_job_arrival_edf j1 j2 hsame, hep_job_arrival_edf j2 j1 hsame']
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq,
        decide_eq_false_iff_not]
      omega')) t hs

end SequentialEDF

end Prosa.Analysis.Facts.Priority.Edf
