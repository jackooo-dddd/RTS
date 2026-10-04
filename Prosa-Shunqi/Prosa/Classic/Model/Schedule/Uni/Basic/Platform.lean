-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/basic/platform.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 51)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Properties of the uniprocessor platform (Rocq module `Platform`).

Representation notes: Boolean tests in proposition position are `= true`; a Boolean chain
`a <= t < b` in proposition position is `(decide (a ≤ t) && decide (t < b)) = true`; the section-local `Let`s
(`job_backlogged_at`, `job_pending_at`, `job_completed_by`) are unfolded. Binder lists follow the Rocq contract
(`job_never_backlogged_response_time_holds` takes only `H_jobs_must_arrive_to_execute` and
`H_j_is_never_backlogged`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def work_conserving {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) : Prop :=
  ∀ j t, arrives_in arr_seq j → backlogged job_arrival job_cost sched j t = true →
    ∃ j_other, scheduled_at sched j_other t = true

def respects_FP_policy {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (higher_eq_priority : FP_policy sporadic_task) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority j_hp j = true

def respects_JLDP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority t j_hp j = true

theorem job_never_backlogged_response_time_holds {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (j : Job)
    (H_j_is_never_backlogged : ∀ t,
      (decide (job_arrival j ≤ t) && decide (t < job_arrival j + job_cost j)) = true →
      ¬ backlogged job_arrival job_cost sched j t = true) :
    ∀ R : Nat, job_cost j ≤ R → completed_by job_cost sched j (job_arrival j + R) = true := by
  intro R GECOST
  -- the service before time t ≥ a_j is the service since a_j
  have hsince : ∀ t, job_arrival j ≤ t →
      service sched j t = ∑ x ∈ Finset.Ico (job_arrival j) t, service_at sched j x := by
    intro t ht
    unfold service service_during
    exact ignore_service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute j 0 t (Nat.zero_le _) ht
  -- j is scheduled at every instant of [a_j, a_j + c_j)
  have hsched : ∀ t, job_arrival j ≤ t → t < job_arrival j + job_cost j → scheduled_at sched j t = true := by
    intro t h1 h2
    by_contra NS
    apply H_j_is_never_backlogged t (by simp [h1, h2])
    have hle := cumulative_service_le_delta sched j (job_arrival j) (t - job_arrival j)
    have heq : job_arrival j + (t - job_arrival j) = t := by omega'
    rw [heq] at hle
    unfold service_during at hle
    rw [← hsince t h1] at hle
    simp only [Bool.not_eq_true] at NS
    simp only [backlogged, pending, has_arrived, completed_by, NS, decide_eq_true_eq, Bool.not_false,
      Bool.and_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
    exact ⟨h1, by omega'⟩
  simp only [completed_by, decide_eq_true_eq]
  rw [hsince _ (Nat.le_add_right _ _)]
  calc job_cost j = ∑ _x ∈ Finset.Ico (job_arrival j) (job_arrival j + job_cost j), 1 := by simp
    _ = ∑ x ∈ Finset.Ico (job_arrival j) (job_arrival j + job_cost j), service_at sched j x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_Ico] at hx
        simp [service_at, hsched x hx.1 hx.2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico (Nat.le_refl _) (by omega')) (fun _ _ _ => Nat.zero_le _)

end Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform
