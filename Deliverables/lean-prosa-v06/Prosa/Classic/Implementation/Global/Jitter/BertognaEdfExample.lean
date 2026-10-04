-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/global/jitter/bertogna_edf_example.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 190)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Platform
import Prosa.Classic.Analysis.Global.Jitter.WorkloadBound
import Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundEdf
import Prosa.Classic.Analysis.Global.Jitter.BertognaEdfComp
import Prosa.Classic.Implementation.Global.Jitter.Job
import Prosa.Classic.Implementation.Global.Jitter.Task
import Prosa.Classic.Implementation.Global.Jitter.Schedule
import Prosa.Classic.Implementation.Global.Jitter.ArrivalSequence

/-!
A global EDF response-time analysis example with release jitter (Rocq module `ResponseTimeAnalysisEDF` of
`classic/implementation/global/jitter/bertogna_edf_example.v`).

Representation notes:
* The section-local `Let`s that define the concrete example (`tsk1`, `tsk2`, `tsk3`, `ts`, `arr_seq`, `sched`) are
  kept as `LEAN_HELPER` definitions of the same names (`ts` is built with the `Program` obligation
  `ts_obligation_1` of the source, proved by `decide`); `num_cpus := 2`, `schedulability_test` and
  `no_deadline_missed_by` are unfolded.
* Concrete jobs and tasks use the jitter-aware `ConcreteJob`/`ConcreteTask` records, whose fields are the job and task
  parameter functions. The task set is used as its underlying list `ts.val` where the Rocq source coerces it to a
  sequence.
* `schedulability_test_succeeds` is checked by `decide` (kernel evaluation of the fixed-point iteration, which the
  Rocq script unfolds step by step; no `native_decide`; the elaborator's `maxRecDepth` is raised for that one
  theorem). The transitivity of the EDF order is proved directly (the Rocq script reuses `RM_is_transitive`, which
  applies by unfolding).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Global.Jitter.BertognaEdfExample.ResponseTimeAnalysisEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule (schedule)
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability (task_misses_no_deadline)
open Prosa.Classic.Analysis.Global.Jitter.BertognaEdfComp.ResponseTimeIterationEDF
  (edf_schedulable taskset_schedulable_by_edf_rta)
open Prosa.Classic.Implementation.Global.Jitter.Job.ConcreteJob
open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask
open Prosa.Classic.Implementation.Global.Jitter.ArrivalSequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler

/-! ### The example (LEAN_HELPER definitions for the section `Let`s) -/

/-- LEAN_HELPER (Rocq `Let tsk1`). -/
def tsk1 : concrete_task := { task_id := 1, task_cost := 2, task_period := 5, task_deadline := 3, task_jitter := 1 }
/-- LEAN_HELPER (Rocq `Let tsk2`). -/
def tsk2 : concrete_task := { task_id := 2, task_cost := 4, task_period := 6, task_deadline := 5, task_jitter := 0 }
/-- LEAN_HELPER (Rocq `Let tsk3`). -/
def tsk3 : concrete_task := { task_id := 3, task_cost := 2, task_period := 12, task_deadline := 11, task_jitter := 2 }

theorem ts_obligation_1 : [tsk1, tsk2, tsk3].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _`). -/
def ts : concrete_taskset := ⟨[tsk1, tsk2, tsk3], ts_obligation_1⟩

theorem ts_has_valid_parameters :
    valid_sporadic_taskset concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline ts.val := by
  intro tsk IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ts_has_constrained_deadlines :
    ∀ tsk, tsk ∈ ts → concrete_task.task_deadline tsk ≤ concrete_task.task_period tsk := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

set_option maxRecDepth 100000 in
theorem schedulability_test_succeeds :
    edf_schedulable concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
      concrete_task.task_jitter 2 ts.val = true := by
  decide

/-- LEAN_HELPER (Rocq `Let arr_seq`). -/
def arr_seq : arrival_sequence concrete_job := periodic_arrival_sequence ts

/-- LEAN_HELPER (Rocq `Let sched`, with `num_cpus := 2`). -/
def sched : schedule concrete_job 2 :=
  scheduler concrete_job.job_arrival concrete_job.job_cost concrete_job.job_jitter 2 arr_seq
    (JLFP_to_JLDP (EDF concrete_job.job_arrival concrete_job.job_deadline))

theorem ts_is_schedulable :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
        concrete_job.job_task arr_seq sched tsk := by
  intro tsk IN
  have CONS := periodic_arrivals_are_consistent ts
  have SET := periodic_arrivals_is_a_set ts ts_has_valid_parameters
  exact taskset_schedulable_by_edf_rta concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
    concrete_task.task_jitter concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
    concrete_job.job_task concrete_job.job_jitter 2 ts
    ts_has_valid_parameters ts_has_constrained_deadlines (periodic_arrivals_all_jobs_from_taskset ts)
    (periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters) (periodic_arrivals_are_sporadic ts)
    sched (by decide)
    (scheduler_jobs_come_from_arrival_sequence _ _ _ _ _ _)
    (scheduler_jobs_execute_after_jitter _ _ _ _ _ _)
    (scheduler_completed_jobs_dont_execute _ _ _ _ _ CONS SET _)
    (scheduler_sequential_jobs _ _ _ _ _ CONS SET _)
    (scheduler_work_conserving _ _ _ _ _ CONS _)
    (scheduler_respects_policy _ _ _ _ _ CONS _
      (fun t y x z h1 h2 => by
        simp only [JLFP_to_JLDP, EDF, decide_eq_true_eq] at h1 h2 ⊢
        exact Nat.le_trans h1 h2)
      (fun t j1 j2 => by
        rcases Nat.le_total (j1.job_arrival + j1.job_deadline) (j2.job_arrival + j2.job_deadline) with h | h
        · simp [JLFP_to_JLDP, EDF, h]
        · simp [JLFP_to_JLDP, EDF, h]))
    schedulability_test_succeeds tsk IN

end Prosa.Classic.Implementation.Global.Jitter.BertognaEdfExample.ResponseTimeAnalysisEDF
