-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/jitter/fp_rta_example.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 154)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Analysis.Uni.Jitter.WorkloadBoundFp
import Prosa.Classic.Analysis.Uni.Jitter.FpRtaComp
import Prosa.Classic.Implementation.Uni.Jitter.Job
import Prosa.Classic.Implementation.Uni.Jitter.Task
import Prosa.Classic.Implementation.Uni.Jitter.ArrivalSequence
import Prosa.Classic.Implementation.Uni.Jitter.Schedule

/-!
A jitter-aware uniprocessor FP response-time analysis example (Rocq module `ResponseTimeAnalysisFP` of
`classic/implementation/uni/jitter/fp_rta_example.v`).

Representation notes:
* The section-local `Let`s that define the concrete example (`tsk1`, `tsk2`, `tsk3`, `ts`, `arr_seq`,
  `higher_eq_priority`, `sched`) are kept as `LEAN_HELPER` definitions of the same names (`ts` is built with the
  `Program` obligation `ts_obligation_1` of the source, proved by `decide`); `sched` takes the section variable
  `job_jitter`. The other `Let`s (`RTA_claimed_bounds`, `schedulability_test`, `no_deadline_missed_by`) are
  unfolded.
* Concrete jobs and tasks use the accepted jitter-aware `ConcreteJob`/`ConcreteTask` records, whose fields are
  the job and task parameter functions. The task set is used as its underlying list `ts.val` where the Rocq source
  coerces it to a sequence.
* `RTA_yields_these_bounds` and `schedulability_test_succeeds` are checked by `decide` (kernel evaluation of the
  fixed-point iteration; no `native_decide`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Jitter.FpRtaExample.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Arrival.Jitter.Job.JobWithJitter (job_jitter_leq_task_jitter)
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule)
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability (task_misses_no_deadline)
open Prosa.Classic.Analysis.Uni.Jitter.FpRtaComp.ResponseTimeIterationFP
  (fp_claimed_bounds fp_schedulable taskset_schedulable_by_fp_rta)
open Prosa.Classic.Implementation.Uni.Jitter.Job.ConcreteJob
open Prosa.Classic.Implementation.Uni.Jitter.Task.ConcreteTask
open Prosa.Classic.Implementation.Uni.Jitter.ArrivalSequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Jitter.Schedule.ConcreteScheduler

/-! ### The example (LEAN_HELPER definitions for the section `Let`s) -/

/-- LEAN_HELPER (Rocq `Let tsk1`). -/
def tsk1 : concrete_task := { task_id := 1, task_cost := 1, task_period := 5, task_deadline := 6, task_jitter := 1 }
/-- LEAN_HELPER (Rocq `Let tsk2`). -/
def tsk2 : concrete_task := { task_id := 2, task_cost := 1, task_period := 5, task_deadline := 6, task_jitter := 0 }
/-- LEAN_HELPER (Rocq `Let tsk3`). -/
def tsk3 : concrete_task := { task_id := 3, task_cost := 1, task_period := 6, task_deadline := 6, task_jitter := 1 }

theorem ts_obligation_1 : [tsk1, tsk2, tsk3].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _`). -/
def ts : concrete_taskset := ⟨[tsk1, tsk2, tsk3], ts_obligation_1⟩

theorem ts_has_positive_costs : ∀ tsk, tsk ∈ ts → 0 < concrete_task.task_cost tsk := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

theorem ts_has_positive_periods : ∀ tsk, tsk ∈ ts → 0 < concrete_task.task_period tsk := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

theorem RTA_yields_these_bounds :
    fp_claimed_bounds concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
      concrete_task.task_jitter (RM concrete_task.task_period) ts.val = some [(tsk1, 2), (tsk2, 2), (tsk3, 3)] := by
  decide

theorem schedulability_test_succeeds :
    fp_schedulable concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
      concrete_task.task_jitter (RM concrete_task.task_period) ts.val = true := by
  unfold fp_schedulable
  rw [RTA_yields_these_bounds]
  rfl

/-- LEAN_HELPER (Rocq `Let arr_seq`). -/
def arr_seq : arrival_sequence concrete_job := periodic_arrival_sequence ts

/-- LEAN_HELPER (Rocq `Let higher_eq_priority`). -/
def higher_eq_priority : JLDP_policy concrete_job := FP_to_JLDP concrete_job.job_task (RM concrete_task.task_period)

/-- LEAN_HELPER (Rocq `Let sched`, which uses the section variable `job_jitter`). -/
def sched (job_jitter : concrete_job → time) : schedule concrete_job :=
  scheduler concrete_job.job_arrival concrete_job.job_cost job_jitter arr_seq higher_eq_priority

theorem ts_is_schedulable (job_jitter : concrete_job → time)
    (H_jitter_is_bounded : ∀ j, arrives_in arr_seq j →
      job_jitter_leq_task_jitter concrete_task.task_jitter job_jitter concrete_job.job_task j = true) :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
        concrete_job.job_task arr_seq (sched job_jitter) tsk := by
  intro tsk IN
  have CONS := periodic_arrivals_are_consistent ts
  exact taskset_schedulable_by_fp_rta concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
    concrete_task.task_jitter concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline job_jitter
    concrete_job.job_task ts.val ts_has_positive_costs ts_has_positive_periods arr_seq CONS
    (periodic_arrivals_is_a_set ts) (periodic_arrivals_all_jobs_from_taskset ts) (periodic_arrivals_are_sporadic ts)
    (periodic_arrivals_job_cost_le_task_cost ts)
    (fun j ARR => of_decide_eq_true (H_jitter_is_bounded j ARR))
    (periodic_arrivals_job_deadline_eq_task_deadline ts) (RM concrete_task.task_period)
    (RM_is_reflexive _) (RM_is_transitive _) (sched job_jitter)
    (scheduler_jobs_come_from_arrival_sequence _ _ _ _ _)
    (scheduler_jobs_execute_after_jitter _ _ _ _ _)
    (scheduler_completed_jobs_dont_execute _ _ _ _ _)
    (scheduler_work_conserving _ _ _ _ CONS _)
    (scheduler_respects_policy _ _ _ _ CONS higher_eq_priority
      (fun t y x z h1 h2 => RM_is_transitive concrete_task.task_period _ _ _ h1 h2)
      (fun j1 j2 t _ _ => by
        rcases Nat.le_total j1.job_task.task_period j2.job_task.task_period with h | h
        · simp [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, h]
        · simp [higher_eq_priority, FP_to_JLDP, FP_to_JLFP, RM, h]))
    schedulability_test_succeeds tsk IN

end Prosa.Classic.Implementation.Uni.Jitter.FpRtaExample.ResponseTimeAnalysisFP
