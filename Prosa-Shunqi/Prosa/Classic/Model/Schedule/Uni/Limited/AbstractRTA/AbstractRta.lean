-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/abstract_RTA/abstract_rta.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 122)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.SufficientConditionForLockInService
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace

/-!
Abstract response-time analysis (Rocq module `AbstractRTA`).

Representation notes: the section-local `Let`s (`work_conserving`, `busy_intervals_are_bounded_by`,
`job_interference_is_bounded_by`, `cumul_interference`, `cumul_interfering_workload`, `busy_interval`,
`response_time_bounded_by`, `is_in_search_space`, `A := job_arrival j - t1`, `job_last`, `optimism`) are unfolded;
Boolean tests in proposition position are `= true`. Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractRta.AbstractRTA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.SufficientConditionForLockInService.AbstractRTALockInService
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace.AbstractRTAReduction

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-- LEAN_HELPER: the job arrives within its busy interval. -/
private theorem busy_bounds {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job)
    (interference : Job → time → Bool) (interfering_workload : Job → time → time) (j : Job) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) : t1 ≤ job_arrival j ∧ job_arrival j < t2 := by
  obtain ⟨⟨IN, _, _⟩, _⟩ := H_busy_interval
  simp only [Bool.and_eq_true] at IN
  exact ⟨of_decide_eq_true IN.1, of_decide_eq_true IN.2⟩

/-- LEAN_HELPER: the busy interval of `j` is bounded by `L`. -/
private theorem busy_le_L {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (L : time) (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) :
    t2 ≤ t1 + L := by
  obtain ⟨t1', t2', _, BOUND, BUSY⟩ := H_busy_interval_exists j H_j_arrives H_job_of_tsk
    (of_decide_eq_true H_job_cost_positive)
  obtain ⟨E1, E2⟩ := busy_interval_is_unique job_arrival job_cost sched interference interfering_workload j t1 t2 t1' t2'
    H_busy_interval BUSY
  subst E1 E2
  exact BOUND

/-- LEAN_HELPER: no service before the arrival. -/
private theorem service_before_arrival {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (j : Job)
    (t : Nat) (h : t ≤ job_arrival j) : service sched j t = 0 := by
  unfold service service_during
  exact cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0 t h

theorem t2_le_arrival_plus_R {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (tsk : Task) (task_lock_in_service : Task → time) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (R : Nat) (j : Job) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (A_sp F_sp : time) (H_A_gt_Asp : A_sp ≤ (job_arrival j - t1)) (H_R_gt_Fsp : F_sp + (task_cost tsk - task_lock_in_service tsk) ≤ R) (H_big_fixpoint_solution : t2 ≤ t1 + (A_sp + F_sp)) :
    t2 ≤ job_arrival j + R := by
  have B := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2 H_busy_interval
  omega'

theorem job_completed_by_arrival_plus_R_1 {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (tsk : Task) (task_lock_in_service : Task → time) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (R : Nat) (j : Job) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (A_sp F_sp : time) (H_A_gt_Asp : A_sp ≤ (job_arrival j - t1)) (H_R_gt_Fsp : F_sp + (task_cost tsk - task_lock_in_service tsk) ≤ R) (H_big_fixpoint_solution : t2 ≤ t1 + (A_sp + F_sp)) :
    completed_by job_cost sched j (job_arrival j + R) = true :=
  completion_monotonic job_cost sched j t2 _
    (t2_le_arrival_plus_R task_cost job_arrival job_cost sched tsk task_lock_in_service interference
      interfering_workload R j t1 t2 H_busy_interval A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_big_fixpoint_solution)
    (job_completes_within_busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2
      H_busy_interval)

theorem solution_for_A_exists' {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task) (task_lock_in_service : Task → time) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (L : time) (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (interference_bound_function : Task → time → time → time) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) (A_sp F_sp : time) (H_A_gt_Asp : A_sp ≤ (job_arrival j - t1)) (H_equivalent : are_equivalent_at_values_less_than (interference_bound_function tsk (job_arrival j - t1)) (interference_bound_function tsk A_sp) L) (H_fixpoint : A_sp + F_sp = task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp)) (H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2)
    (H_fixpoint_is_no_less_than_relative_arrival_of_j : (job_arrival j - t1) ≤ A_sp + F_sp) :
    ∃ F, A_sp + F_sp = (job_arrival j - t1) + F ∧ F ≤ F_sp ∧
      (job_arrival j - t1) + F = task_lock_in_service tsk + interference_bound_function tsk (job_arrival j - t1) ((job_arrival j - t1) + F) := by
  have LEL := busy_le_L job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L
    H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
  exact solution_for_A_exists tsk L (fun tsk A R => task_lock_in_service tsk + interference_bound_function tsk A R)
    A_sp F_sp (by omega') H_fixpoint (job_arrival j - t1)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨H_A_gt_Asp, H_fixpoint_is_no_less_than_relative_arrival_of_j⟩)
    (fun x hx => by simp only; rw [H_equivalent x hx])

theorem job_completed_by_arrival_plus_R_2 {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq) (tsk : Task) (job_lock_in_service : Job → time) (task_lock_in_service : Task → time) (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service : proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload) (L : time)
    (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (interference_bound_function : Task → time → time → time)
    (H_job_interference_is_bounded : job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload interference_bound_function) (R : Nat) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) (A_sp F_sp : time) (H_A_gt_Asp : A_sp ≤ (job_arrival j - t1)) (H_equivalent : are_equivalent_at_values_less_than (interference_bound_function tsk (job_arrival j - t1)) (interference_bound_function tsk A_sp) L) (H_fixpoint : A_sp + F_sp = task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp)) (H_R_gt_Fsp : F_sp + (task_cost tsk - task_lock_in_service tsk) ≤ R) (H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2)
    (H_fixpoint_is_no_less_than_relative_arrival_of_j : (job_arrival j - t1) ≤ A_sp + F_sp) :
    completed_by job_cost sched j (job_arrival j + R) = true := by
  obtain ⟨PRJ1, PRJ2, PRJ3⟩ := H_proper_job_lock_in_service
  obtain ⟨PRT1, PRT2⟩ := H_proper_task_lock_in_service
  have B := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2 H_busy_interval
  obtain ⟨F, EQSUM, F2LEF1, FIX2⟩ := solution_for_A_exists' job_arrival job_cost job_task arr_seq sched tsk
    task_lock_in_service interference interfering_workload L H_busy_interval_exists interference_bound_function j
    H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval A_sp F_sp H_A_gt_Asp H_equivalent H_fixpoint
    H_small_fixpoint_solution H_fixpoint_is_no_less_than_relative_arrival_of_j
  have LIS_LE_T := PRT2 j H_j_arrives H_job_of_tsk
  have LIS_LE_C := PRJ2 j H_j_arrives H_job_cost_positive
  have CLE := H_job_cost_le_task_cost j H_j_arrives
  simp only [job_cost_le_task_cost, decide_eq_true_eq, H_job_of_tsk] at CLE
  unfold task_lock_in_service_le_task_cost at PRT1
  by_contra CONTRc
  -- the interference in [t1, t1 + (A + F)) is bounded by the interference bound function
  have NOTCOMP : (!completed_by job_cost sched j (t1 + ((job_arrival j - t1) + F))) = true := by
    cases hc : completed_by job_cost sched j (t1 + ((job_arrival j - t1) + F))
    · rfl
    · exfalso; apply CONTRc
      exact completion_monotonic job_cost sched j _ _ (by omega') hc
  have IB := H_job_interference_is_bounded t1 t2 ((job_arrival j - t1) + F) j H_busy_interval (by omega') H_j_arrives H_job_of_tsk
    NOTCOMP
  simp only at IB
  -- before the arrival of `j`, the job is interfered at every instant
  have Fact0 : (job_arrival j - t1) ≤ cumul_interference interference j t1 (t1 + ((job_arrival j - t1) + F)) := by
    unfold cumul_interference
    rw [← Finset.sum_Ico_consecutive _ (Nat.le_add_right t1 (job_arrival j - t1)) (by omega' : t1 + (job_arrival j - t1) ≤ t1 + ((job_arrival j - t1) + F))]
    calc (job_arrival j - t1) = ∑ _x ∈ Finset.Ico t1 (t1 + (job_arrival j - t1)), (1 : Nat) := by simp
      _ ≤ ∑ x ∈ Finset.Ico t1 (t1 + (job_arrival j - t1)), (interference j x).toNat := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_Ico] at hx
          have WC := H_work_conserving j t1 t2 x H_j_arrives H_job_of_tsk (of_decide_eq_true H_job_cost_positive)
            H_busy_interval (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
          cases hi : interference j x
          · exfalso
            have SCHED := WC.mp (by rw [hi]; simp)
            have := of_decide_eq_true (H_jobs_must_arrive_to_execute j x SCHED)
            omega'
          · simp
      _ ≤ _ := Nat.le_add_right _ _
  have FleTLIN : task_lock_in_service tsk ≤ F := by omega'
  -- `j` reaches its lock-in service by `t1 + (A + F - optimism)`
  have ESERV := j_receives_at_least_lock_in_service job_arrival job_cost job_task arr_seq sched tsk interference
    interfering_workload H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
    (job_lock_in_service j) LIS_LE_C ((job_arrival j - t1) + F - (task_lock_in_service tsk - job_lock_in_service j)) (by
      have M : cumul_interference interference j t1
          (t1 + ((job_arrival j - t1) + F - (task_lock_in_service tsk - job_lock_in_service j))) ≤
          cumul_interference interference j t1 (t1 + ((job_arrival j - t1) + F)) := by
        unfold cumul_interference
        exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl _) (by omega'))
      omega')
  have COMPL := job_completes_after_reaching_lock_in_service job_cost arr_seq sched j H_j_arrives H_job_cost_positive
    H_completed_jobs_dont_execute job_lock_in_service PRJ2 PRJ3 _ ESERV
  exact CONTRc (completion_monotonic job_cost sched j _ _ (by omega') COMPL)

theorem relative_arrival_is_bounded {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (L : time) (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) :
    (job_arrival j - t1) < L := by
  have LEL := busy_le_L job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L
    H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
  have B := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2 H_busy_interval
  omega'

theorem service_of_job_ge_lock_in_service {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (tsk : Task) (job_lock_in_service : Job → time) (task_lock_in_service : Task → time) (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service : proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload) (L : time)
    (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (interference_bound_function : Task → time → time → time)
    (H_job_interference_is_bounded : job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload interference_bound_function) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) (A_sp F_sp : time) (H_equivalent : are_equivalent_at_values_less_than (interference_bound_function tsk (job_arrival j - t1)) (interference_bound_function tsk A_sp) L) (H_fixpoint : A_sp + F_sp = task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp)) (H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2)
    (H_fixpoint_is_less_that_relative_arrival_of_j : A_sp + F_sp < (job_arrival j - t1)) :
    job_lock_in_service j ≤ service sched j (t1 + (A_sp + F_sp)) := by
  obtain ⟨PRJ1, PRJ2, PRJ3⟩ := H_proper_job_lock_in_service
  obtain ⟨PRT1, PRT2⟩ := H_proper_task_lock_in_service
  have B := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2 H_busy_interval
  have ALTT := relative_arrival_is_bounded job_arrival job_cost job_task arr_seq sched tsk interference
    interfering_workload L H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
  have NOTCOMP : (!completed_by job_cost sched j (t1 + (A_sp + F_sp))) = true := by
    have Z := service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute j (t1 + (A_sp + F_sp)) (by omega')
    have POS := of_decide_eq_true H_job_cost_positive
    simp only [completed_by, Z, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
    exact POS
  have IB := H_job_interference_is_bounded t1 t2 (A_sp + F_sp) j H_busy_interval H_small_fixpoint_solution H_j_arrives
    H_job_of_tsk NOTCOMP
  simp only at IB
  rw [H_equivalent (A_sp + F_sp) (by omega')] at IB
  have LT := PRT2 j H_j_arrives H_job_of_tsk
  exact j_receives_at_least_lock_in_service job_arrival job_cost job_task arr_seq sched tsk interference
    interfering_workload H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
    (job_lock_in_service j) (PRJ2 j H_j_arrives H_job_cost_positive) (A_sp + F_sp) (by omega')

theorem relative_arrival_time_is_no_less_than_fixpoint {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (tsk : Task) (job_lock_in_service : Job → time) (task_lock_in_service : Task → time) (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service : proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload) (L : time)
    (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (interference_bound_function : Task → time → time → time)
    (H_job_interference_is_bounded : job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload interference_bound_function) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) (A_sp F_sp : time) (H_equivalent : are_equivalent_at_values_less_than (interference_bound_function tsk (job_arrival j - t1)) (interference_bound_function tsk A_sp) L) (H_fixpoint : A_sp + F_sp = task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp)) (H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2)
    (H_fixpoint_is_less_that_relative_arrival_of_j : A_sp + F_sp < (job_arrival j - t1)) : False := by
  have ESERV := service_of_job_ge_lock_in_service task_cost job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute tsk job_lock_in_service task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service interference interfering_workload H_work_conserving L H_busy_interval_exists interference_bound_function H_job_interference_is_bounded j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval A_sp F_sp H_equivalent H_fixpoint H_small_fixpoint_solution H_fixpoint_is_less_that_relative_arrival_of_j
  have B := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2 H_busy_interval
  have Z := service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute j (t1 + (A_sp + F_sp)) (by omega')
  have POS := H_proper_job_lock_in_service.1 j H_j_arrives H_job_cost_positive
  omega'

theorem uniprocessor_response_time_bound {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq) (tsk : Task) (job_lock_in_service : Job → time) (task_lock_in_service : Task → time) (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service : proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload) (L : time)
    (H_busy_interval_exists : busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L) (interference_bound_function : Task → time → time → time)
    (H_job_interference_is_bounded : job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload interference_bound_function) (R : Nat)
    (H_R_is_maximum : ∀ A, is_in_search_space tsk L interference_bound_function A →
      ∃ F, A + F = task_lock_in_service tsk + interference_bound_function tsk A (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro j ARR JOBtsk
  unfold is_response_time_bound_of_job
  rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
  · simp [completed_by, ZERO]
  have POSb : job_cost_positive job_cost j = true := decide_eq_true POS
  obtain ⟨t1, t2, NEQ, H2, BUSY⟩ := H_busy_interval_exists j ARR JOBtsk POS
  have A2LTL := relative_arrival_is_bounded job_arrival job_cost job_task arr_seq sched tsk interference
    interfering_workload L H_busy_interval_exists j ARR JOBtsk POSb t1 t2 BUSY
  obtain ⟨A1, ALEA2, EQΦ, INSP⟩ := representative_exists tsk L interference_bound_function _ A2LTL
  obtain ⟨F1, FIX1, LE1⟩ := H_R_is_maximum A1 INSP
  by_cases BIG : t2 ≤ t1 + (A1 + F1)
  · exact job_completed_by_arrival_plus_R_1 task_cost job_arrival job_cost sched tsk task_lock_in_service interference
      interfering_workload R j t1 t2 BUSY A1 F1 ALEA2 LE1 BIG
  · by_cases BOUND : job_arrival j - t1 ≤ A1 + F1
    · exact job_completed_by_arrival_plus_R_2 task_cost job_arrival job_cost job_task arr_seq sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_job_cost_le_task_cost tsk job_lock_in_service
        task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service interference interfering_workload
        H_work_conserving L H_busy_interval_exists interference_bound_function H_job_interference_is_bounded R j ARR
        JOBtsk POSb t1 t2 BUSY A1 F1 ALEA2 EQΦ FIX1 LE1 (by omega') BOUND
    · exact (relative_arrival_time_is_no_less_than_fixpoint task_cost job_arrival job_cost job_task arr_seq sched
        H_jobs_must_arrive_to_execute tsk job_lock_in_service task_lock_in_service H_proper_job_lock_in_service
        H_proper_task_lock_in_service interference interfering_workload H_work_conserving L H_busy_interval_exists
        interference_bound_function H_job_interference_is_bounded j ARR JOBtsk POSb t1 t2 BUSY A1 F1 EQΦ FIX1
        (by omega') (by omega')).elim

end Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractRta.AbstractRTA
