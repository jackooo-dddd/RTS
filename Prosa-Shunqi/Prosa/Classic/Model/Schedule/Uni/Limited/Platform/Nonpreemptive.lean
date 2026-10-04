-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/platform/nonpreemptive.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 104)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions

/-!
The fully nonpreemptive model as a limited-preemption platform (Rocq module `FullyNonPreemptivePlatform`).

Representation notes: `x == y` is `decide (x = y)`; `maxn` is `max`; `ε` is the v0.6 util notation for `1`; the
section-local `Let`s (`job_pending`, `job_completed_by`, `job_scheduled_at`, `job_max_nps := job_cost`,
`task_max_nps := task_cost`) are unfolded (`job_max_nps`/`task_max_nps` as `fun j => job_cost j` /
`fun tsk => task_cost tsk`). `Require Export …limited.platform.definitions` is an `import`. Binder lists follow the
Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Util.Epsilon

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def can_be_preempted_for_fully_nonpreemptive_model {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (j : Job)
    (progr : time) : Bool :=
  decide (progr = 0) || decide (progr = job_cost j)

private theorem service_step {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat) :
    service sched j (t + 1) = service sched j t + service_at sched j t := by
  unfold service service_during
  rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]

/-- LEAN_HELPER: positive service before `t` means `j` was scheduled at some `ft < t`. -/
private theorem scheduled_before {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat)
    (POS : 0 < service sched j t) : ∃ ft, ft < t ∧ scheduled_at sched j ft = true := by
  obtain ⟨ft, H, S, _⟩ := incremental_service_during sched j 0 t 0 POS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  exact ⟨ft, H.2, S⟩

theorem fully_nonpreemptive_model_is_correct {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_nonpreemptive_sched :
      Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule.NonpreemptiveSchedule.is_nonpreemptive_schedule job_cost
        sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) :
    correct_preemption_model arr_seq sched (can_be_preempted_for_fully_nonpreemptive_model job_cost) := by
  intro j _
  constructor
  · intro t NP
    simp only [can_be_preempted_for_fully_nonpreemptive_model, Bool.not_or, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at NP
    obtain ⟨NZ, NC⟩ := NP
    have LEc := H_completed_jobs_dont_execute j t
    obtain ⟨ft, LT, SCHED⟩ := scheduled_before sched j t (by omega')
    apply H_nonpreemptive_sched j ft t (by omega') SCHED
    simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not]
    omega'
  · intro prt NSCHED SCHED
    simp only [can_be_preempted_for_fully_nonpreemptive_model, Bool.or_eq_true, decide_eq_true_eq]
    left
    by_contra POS
    obtain ⟨ft, LT, SCHEDft⟩ := scheduled_before sched j (prt + 1) (by omega')
    have S2 := service_step sched j (prt + 1)
    have S1 := service_step sched j prt
    have LEc := H_completed_jobs_dont_execute j (prt + 1 + 1)
    have hs1 : service_at sched j (prt + 1) = 1 := by simp [service_at, SCHED]
    have NCprt : (!completed_by job_cost sched j prt) = true := by
      simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not]
      have : service_at sched j prt ≤ 1 := by unfold service_at; cases scheduled_at sched j prt <;> simp
      omega'
    have := H_nonpreemptive_sched j ft prt (by omega') SCHEDft NCprt
    simp only [this, Bool.not_true] at NSCHED
    exact Bool.noConfusion NSCHED

theorem fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq) :
    model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq
      (can_be_preempted_for_fully_nonpreemptive_model job_cost) (fun j => job_cost j) (fun tsk => task_cost tsk) := by
  intro j ARRj
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [job_cannot_become_nonpreemptive_before_execution, can_be_preempted_for_fully_nonpreemptive_model]
  · simp [job_cannot_be_nonpreemptive_after_completion, can_be_preempted_for_fully_nonpreemptive_model]
  · intro ARR
    have := H_job_cost_le_task_cost j ARR
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    exact this
  · intro progr H
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    rcases Nat.eq_zero_or_pos progr with EQ | GT
    · refine ⟨progr, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'
      · simp [can_be_preempted_for_fully_nonpreemptive_model, EQ]
    · refine ⟨job_cost j, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'
      · simp [can_be_preempted_for_fully_nonpreemptive_model]

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform
