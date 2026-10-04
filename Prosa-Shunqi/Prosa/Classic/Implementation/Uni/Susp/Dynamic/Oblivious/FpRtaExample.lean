-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/susp/dynamic/oblivious/fp_rta_example.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 179)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Analysis.Uni.Basic.WorkloadBoundFp
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.FpRta
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.ArrivalSequence
import Prosa.Classic.Implementation.Uni.Susp.Schedule

/-!
A suspension-oblivious FP response-time analysis example (Rocq module `ResponseTimeAnalysisFP` of
`classic/implementation/uni/susp/dynamic/oblivious/fp_rta_example.v`).

Representation notes:
* The section-local `Let`s that define the concrete example (`tsk1`, `tsk2`, `tsk3`, `ts`, `arr_seq`,
  `higher_eq_priority`, `sched`) are kept as `LEAN_HELPER` definitions of the same names (`ts` is built with the
  `Program` obligation `ts_obligation_1` of the source, proved by `decide`); `sched` takes the section variable
  `next_suspension`. The other `Let`s (`inflated_cost`, `RTA_claimed_bounds`, `schedulability_test`,
  `no_deadline_missed_by`) are unfolded.
* Concrete jobs and tasks use the accepted suspension-aware `ConcreteJob`/`ConcreteTask` records. The task set is
  used as its underlying list `ts.val` where the Rocq source coerces it to a sequence.
* `RTA_yields_these_bounds` is checked by `decide` (kernel evaluation of the fixed-point iteration; no
  `native_decide`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Susp.Dynamic.Oblivious.FpRtaExample.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension (job_suspension dynamic_suspension_model)
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule)
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability (task_misses_no_deadline)
open Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP (fp_claimed_bounds fp_schedulable)
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction.ReductionToBasicSchedule (inflated_task_cost)
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.FpRta.SuspensionObliviousFP
  (suspension_oblivious_fp_rta_implies_schedulability)
open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job.ConcreteJob
open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task.ConcreteTask
open Prosa.Classic.Implementation.Uni.Susp.Dynamic.ArrivalSequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Susp.Schedule.ConcreteScheduler

/-! ### The example (LEAN_HELPER definitions for the section `Let`s) -/

/-- LEAN_HELPER (Rocq `Let tsk1`). -/
def tsk1 : concrete_task :=
  { task_id := 1, task_cost := 1, task_period := 5, task_deadline := 5, task_suspension_bound := 1 }
/-- LEAN_HELPER (Rocq `Let tsk2`). -/
def tsk2 : concrete_task :=
  { task_id := 2, task_cost := 1, task_period := 5, task_deadline := 5, task_suspension_bound := 0 }
/-- LEAN_HELPER (Rocq `Let tsk3`). -/
def tsk3 : concrete_task :=
  { task_id := 3, task_cost := 1, task_period := 6, task_deadline := 6, task_suspension_bound := 1 }

theorem ts_obligation_1 : [tsk1, tsk2, tsk3].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _`). -/
def ts : concrete_taskset := ⟨[tsk1, tsk2, tsk3], ts_obligation_1⟩

theorem ts_has_valid_parameters :
    valid_sporadic_taskset concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline ts.val := by
  intro tsk IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem inflated_cost_le_deadline_and_period :
    ∀ tsk, tsk ∈ ts →
      inflated_task_cost concrete_task.task_cost concrete_task.task_suspension_bound tsk ≤
          concrete_task.task_deadline tsk ∧
        inflated_task_cost concrete_task.task_cost concrete_task.task_suspension_bound tsk ≤
          concrete_task.task_period tsk := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

theorem RTA_yields_these_bounds :
    fp_claimed_bounds (inflated_task_cost concrete_task.task_cost concrete_task.task_suspension_bound)
      concrete_task.task_period concrete_task.task_deadline (RM concrete_task.task_period) ts.val =
      some [(tsk1, 3), (tsk2, 3), (tsk3, 5)] := by
  decide

theorem schedulability_test_succeeds :
    fp_schedulable (inflated_task_cost concrete_task.task_cost concrete_task.task_suspension_bound)
      concrete_task.task_period concrete_task.task_deadline (RM concrete_task.task_period) ts.val = true := by
  unfold fp_schedulable
  rw [RTA_yields_these_bounds]
  rfl

/-- LEAN_HELPER (Rocq `Let arr_seq`). -/
def arr_seq : arrival_sequence concrete_job := periodic_arrival_sequence ts

/-- LEAN_HELPER (Rocq `Let higher_eq_priority`). -/
def higher_eq_priority : JLDP_policy concrete_job := FP_to_JLDP concrete_job.job_task (RM concrete_task.task_period)

/-- LEAN_HELPER (Rocq `Let sched`, which uses the section variable `next_suspension`). -/
def sched (next_suspension : job_suspension concrete_job) : schedule concrete_job :=
  scheduler concrete_job.job_arrival concrete_job.job_cost arr_seq next_suspension higher_eq_priority

theorem ts_is_schedulable (next_suspension : job_suspension concrete_job)
    (H_dynamic_suspensions : dynamic_suspension_model concrete_job.job_cost concrete_job.job_task next_suspension
      concrete_task.task_suspension_bound) :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
        concrete_job.job_task arr_seq (sched next_suspension) tsk := by
  intro tsk IN
  have CONS := periodic_arrivals_are_consistent ts
  have TOTAL : JLDP_is_total arr_seq higher_eq_priority := by
    intro j1 j2 t _ _
    rcases Nat.le_total j1.job_task.task_period j2.job_task.task_period with h | h
    · simp [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, h]
    · simp [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, h]
  exact suspension_oblivious_fp_rta_implies_schedulability concrete_task.task_cost concrete_task.task_period
    concrete_task.task_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
    concrete_job.job_task ts ts_has_valid_parameters arr_seq CONS (periodic_arrivals_is_a_set ts ts_has_valid_parameters)
    (periodic_arrivals_all_jobs_from_taskset ts) (periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters)
    (periodic_arrivals_are_sporadic ts) (RM concrete_task.task_period) (RM_is_reflexive _) (RM_is_transitive _)
    (fun x y _ _ => by
      rcases Nat.le_total x.task_period y.task_period with h | h
      · left; simp [RM, h]
      · right; simp [RM, h])
    next_suspension concrete_task.task_suspension_bound H_dynamic_suspensions inflated_cost_le_deadline_and_period
    (sched next_suspension)
    (scheduler_jobs_come_from_arrival_sequence _ _ _ CONS _ _)
    (scheduler_jobs_must_arrive_to_execute _ _ _ CONS _ _)
    (scheduler_completed_jobs_dont_execute _ _ _ CONS _ _)
    (scheduler_work_conserving _ _ _ CONS _ _)
    (scheduler_respects_policy _ _ _ CONS _ higher_eq_priority
      (fun t y x z h1 h2 => RM_is_transitive concrete_task.task_period _ _ _ h1 h2) TOTAL)
    (scheduler_respects_self_suspensions _ _ _ CONS _ _)
    schedulability_test_succeeds tsk IN

end Prosa.Classic.Implementation.Uni.Susp.Dynamic.Oblivious.FpRtaExample.ResponseTimeAnalysisFP
