-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/basic/fp_rta_example.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 167)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Analysis.Uni.Basic.WorkloadBoundFp
import Prosa.Classic.Analysis.Uni.Basic.FpRtaComp
import Prosa.Classic.Implementation.Job
import Prosa.Classic.Implementation.Task
import Prosa.Classic.Implementation.ArrivalSequence
import Prosa.Classic.Implementation.Uni.Basic.Schedule

/-!
A uniprocessor FP response-time analysis example (Rocq module `ResponseTimeAnalysisFP` of
`classic/implementation/uni/basic/fp_rta_example.v`).

Representation notes:
* The section-local `Let`s that define the concrete example (`tsk1`, `tsk2`, `tsk3`, `ts`, `arr_seq`,
  `higher_eq_priority`, `sched`) are kept as `LEAN_HELPER` definitions of the same names (`ts` is built with the
  `Program` obligation `ts_obligation_1` of the source, proved by `decide`). The other `Let`s
  (`RTA_claimed_bounds`, `schedulability_test`, `no_deadline_missed_by`) are unfolded.
* Concrete jobs and tasks use the accepted `ConcreteJob`/`ConcreteTask` records, whose fields are the job and task
  parameter functions. The task set is used as its underlying list `ts.val` where the Rocq source coerces it to a
  sequence. MathComp's `total R` is `∀ x y, (R x y || R y x) = true`.
* `RTA_yields_these_bounds` is checked by `decide` (kernel evaluation of the fixed-point iteration; no
  `native_decide`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Basic.FpRtaExample.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule)
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability (task_misses_no_deadline)
open Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP
  (fp_claimed_bounds fp_schedulable taskset_schedulable_by_fp_rta)
open Prosa.Classic.Implementation.Job.ConcreteJob
open Prosa.Classic.Implementation.Task.ConcreteTask
open Prosa.Classic.Implementation.ArrivalSequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Basic.Schedule.ConcreteScheduler

/-! ### The example (LEAN_HELPER definitions for the section `Let`s) -/

/-- LEAN_HELPER (Rocq `Let tsk1`). -/
def tsk1 : concrete_task := { task_id := 1, task_cost := 1, task_period := 4, task_deadline := 5 }
/-- LEAN_HELPER (Rocq `Let tsk2`). -/
def tsk2 : concrete_task := { task_id := 2, task_cost := 1, task_period := 6, task_deadline := 5 }
/-- LEAN_HELPER (Rocq `Let tsk3`). -/
def tsk3 : concrete_task := { task_id := 3, task_cost := 1, task_period := 6, task_deadline := 6 }

theorem ts_obligation_1 : [tsk1, tsk2, tsk3].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _`). -/
def ts : concrete_taskset := ⟨[tsk1, tsk2, tsk3], ts_obligation_1⟩

theorem ts_has_valid_parameters :
    valid_sporadic_taskset concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline ts.val := by
  intro tsk IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem RTA_yields_these_bounds :
    fp_claimed_bounds concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
      (RM concrete_task.task_period) ts.val = some [(tsk1, 1), (tsk2, 3), (tsk3, 3)] := by
  decide

theorem schedulability_test_succeeds :
    fp_schedulable concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
      (RM concrete_task.task_period) ts.val = true := by
  unfold fp_schedulable
  rw [RTA_yields_these_bounds]
  rfl

/-- LEAN_HELPER (Rocq `Let arr_seq`). -/
def arr_seq : arrival_sequence concrete_job := periodic_arrival_sequence ts

/-- LEAN_HELPER (Rocq `Let higher_eq_priority`). -/
def higher_eq_priority : JLDP_policy concrete_job := FP_to_JLDP concrete_job.job_task (RM concrete_task.task_period)

theorem priority_is_total : ∀ t : time, ∀ x y, (higher_eq_priority t x y || higher_eq_priority t y x) = true := by
  intro t x y
  rcases Nat.le_total x.job_task.task_period y.job_task.task_period with h | h
  · simp [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, h]
  · simp [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, h]

/-- LEAN_HELPER (Rocq `Let sched`). -/
def sched : schedule concrete_job :=
  scheduler concrete_job.job_arrival concrete_job.job_cost arr_seq higher_eq_priority

theorem ts_is_schedulable :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
        concrete_job.job_task arr_seq sched tsk := by
  intro tsk IN
  have CONS := periodic_arrivals_are_consistent ts
  exact taskset_schedulable_by_fp_rta concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
    concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline concrete_job.job_task ts
    ts_has_valid_parameters arr_seq CONS (periodic_arrivals_is_a_set ts ts_has_valid_parameters)
    (periodic_arrivals_all_jobs_from_taskset ts)
    (periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters) (periodic_arrivals_are_sporadic ts)
    (RM concrete_task.task_period) (RM_is_reflexive _) (RM_is_transitive _) sched
    (scheduler_jobs_come_from_arrival_sequence _ _ _ CONS _)
    (scheduler_jobs_must_arrive_to_execute _ _ _ CONS _)
    (scheduler_completed_jobs_dont_execute _ _ _ CONS _)
    (scheduler_work_conserving _ _ _ CONS _)
    (scheduler_respects_policy _ _ _ CONS higher_eq_priority
      (fun t y x z h1 h2 => RM_is_transitive concrete_task.task_period _ _ _ h1 h2) priority_is_total)
    schedulability_test_succeeds tsk IN

end Prosa.Classic.Implementation.Uni.Basic.FpRtaExample.ResponseTimeAnalysisFP
