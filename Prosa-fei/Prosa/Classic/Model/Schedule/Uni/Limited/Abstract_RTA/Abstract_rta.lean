-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/abstract_RTA/abstract_rta.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Sufficient_condition_for_lock_in_service
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_rta

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space.AbstractRTAReduction
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Sufficient_condition_for_lock_in_service

namespace AbstractRTA

section Abstract_RTA

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

variable (sched : schedule Job)
variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

variable (H_job_cost_le_task_cost :
  cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)

variable (ts : List Task)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (job_lock_in_service : Job → Time)
variable (task_lock_in_service : Task → Time)

variable (H_proper_job_lock_in_service :
  proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)

variable (H_proper_task_lock_in_service :
  proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)

variable (interference : Job → Time → Bool)
variable (interfering_workload : Job → Time → Time)

variable (H_work_conserving :
  work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload)

variable (L : Time)
variable (H_busy_interval_exists :
  busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L)

variable (interference_bound_function : Task → Time → Time → Time)
variable (H_job_interference_is_bounded :
  job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload interference_bound_function)

variable (R : Nat)
variable (H_R_is_maximum :
  ∀ A,
    is_in_search_space tsk L interference_bound_function A →
    ∃ F,
      A + F = task_lock_in_service tsk + interference_bound_function tsk A (A + F) ∧
      F + (task_cost tsk - task_lock_in_service tsk) ≤ R)

section ProofOfTheorem

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost_positive job_cost j)

variable (t1 t2 : Time)
variable (H_busy_interval :
  busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)

variable (A_sp F_sp : Time)
variable (H_A_gt_Asp : A_sp ≤ job_arrival j - t1)
variable (H_equivalent :
  are_equivalent_at_values_less_than (interference_bound_function tsk (job_arrival j - t1)) (interference_bound_function tsk A_sp) L)
variable (H_Asp_is_in_search_space : is_in_search_space tsk L interference_bound_function A_sp)
variable (H_fixpoint :
  A_sp + F_sp = task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp))
variable (H_R_gt_Fsp : F_sp + (task_cost tsk - task_lock_in_service tsk) ≤ R)

section FixpointOutsideBusyInterval

variable (H_big_fixpoint_solution : t2 ≤ t1 + (A_sp + F_sp))

include H_busy_interval H_A_gt_Asp H_R_gt_Fsp H_big_fixpoint_solution in
theorem t2_le_arrival_plus_R :
    t2 ≤ job_arrival j + R := by
  obtain ⟨⟨h_le_arr, h_arr_lt, _, _⟩, _⟩ := H_busy_interval
  have h1 := H_big_fixpoint_solution
  have h2 := H_A_gt_Asp
  have h3 := H_R_gt_Fsp
  unfold Time at *
  omega

include H_completed_jobs_dont_execute H_busy_interval H_A_gt_Asp H_R_gt_Fsp H_big_fixpoint_solution in
theorem job_completed_by_arrival_plus_R_1 :
    completed_by job_cost sched j (job_arrival j + R) := by
  -- First show j completes by t2 (from quiet_time at t2)
  obtain ⟨⟨h_le_arr, h_arr_lt, _, _⟩, _, h_qt2⟩ := H_busy_interval
  -- h_qt2 : ¬ pending_earlier_and_at, and arrived_before j t2 holds
  have h_compl_t2 : completed_by job_cost sched j t2 := by
    by_contra h_not_compl
    exact h_qt2 ⟨h_arr_lt, h_not_compl⟩  -- t2 ≤job_arrival j + R
  have h_t2_le : t2 ≤ job_arrival j + R := by
    calc t2
        ≤ t1 + (A_sp + F_sp) := H_big_fixpoint_solution
      _ ≤ t1 + (job_arrival j - t1 + F_sp) := by simp only [Time] at *; omega
      _ = job_arrival j + F_sp := by simp only [Time] at *; omega
      _ ≤ job_arrival j + R := by simp only [Time] at *; omega
  exact completion_monotonic job_cost sched j t2 (job_arrival j + R) h_t2_le h_compl_t2

end FixpointOutsideBusyInterval

section FixpointInsideBusyInterval

variable (H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2)

section FixpointIsNoLessThanArrival

variable (H_fixpoint_is_no_less_than_relative_arrival_of_j : job_arrival j - t1 ≤ A_sp + F_sp)

include H_work_conserving H_busy_interval_exists H_job_interference_is_bounded
  H_busy_interval H_equivalent H_fixpoint H_small_fixpoint_solution
  H_fixpoint_is_no_less_than_relative_arrival_of_j H_j_arrives H_job_of_tsk H_job_cost_positive H_A_gt_Asp H_Asp_is_in_search_space in
theorem solution_for_A_exists' :
    ∃ F,
      A_sp + F_sp = (job_arrival j - t1) + F ∧
      F ≤ F_sp ∧
      (job_arrival j - t1) + F = task_lock_in_service tsk + interference_bound_function tsk (job_arrival j - t1) ((job_arrival j - t1) + F) := by
  set A := job_arrival j - t1
  refine ⟨A_sp + F_sp - A, ?_, ?_, ?_⟩
  · simp only [Time] at *; omega
  · simp only [Time] at *; omega
  · have hAF : A + (A_sp + F_sp - A) = A_sp + F_sp := by simp only [Time] at *; omega
    rw [hAF]
    -- Need: A_sp + F_sp < L (to use H_equivalent)
    have hLT_L : A_sp + F_sp < L := by
      obtain ⟨t1', t2', _, _, hbound, hbusy'⟩ :=
        H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive
      have ⟨heq1, heq2⟩ := busy_interval_is_unique job_arrival job_cost sched
        interference interfering_workload j t1 t2 t1' t2' H_busy_interval hbusy'
      subst heq1; subst heq2
      simp only [Time] at *; omega
    rw [H_equivalent (A_sp + F_sp) hLT_L]
    exact H_fixpoint
include H_proper_job_lock_in_service H_proper_task_lock_in_service
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_work_conserving H_busy_interval_exists H_job_interference_is_bounded H_job_cost_le_task_cost
  H_busy_interval H_equivalent H_fixpoint H_R_gt_Fsp H_small_fixpoint_solution
  H_fixpoint_is_no_less_than_relative_arrival_of_j H_j_arrives H_job_of_tsk H_job_cost_positive
  H_A_gt_Asp H_Asp_is_in_search_space in
theorem job_completed_by_arrival_plus_R_2 :
    completed_by job_cost sched j (job_arrival j + R) := by
  obtain ⟨hPOS_lis, hLIS_le_cost, hNONPREEMPT⟩ := H_proper_job_lock_in_service
  obtain ⟨hTLIS_le_tcost, hTLIS_bounds⟩ := H_proper_task_lock_in_service
  have hGT := H_busy_interval.1.1
  have hLT_arr := H_busy_interval.1.2.1
  set A := job_arrival j - t1 with hA_def
  set job_last := job_cost j - job_lock_in_service j with hJL_def
  set optimism := task_lock_in_service tsk - job_lock_in_service j with hOPT_def
  -- Get F from solution_for_A_exists'
  obtain ⟨F, hEQSUM, hFleF_sp, hFIX2⟩ :=
    @solution_for_A_exists' Task _ Job _
      job_arrival job_cost job_task arr_seq sched tsk task_lock_in_service
      interference interfering_workload H_work_conserving L H_busy_interval_exists
      interference_bound_function H_job_interference_is_bounded
      j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
      A_sp F_sp H_A_gt_Asp H_equivalent H_Asp_is_in_search_space
      H_fixpoint H_small_fixpoint_solution
      H_fixpoint_is_no_less_than_relative_arrival_of_j
  -- By contradiction
  by_contra CONTRc
  -- Fact1: A ≤ interference_bound_function tsk A (A + F)
  have Fact1 : A ≤ interference_bound_function tsk A (A + F) := by
    -- interference before arrival time is at least A (job gets interference at every step before arrival)
    have hCumul_ge_A : A ≤ cumul_interference interference j t1 (t1 + (A + F)) := by
      simp only [cumul_interference]
      calc A = ∑ _t ∈ Finset.Ico t1 (t1 + A), 1 := by
            simp [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
        _ ≤ ∑ t ∈ Finset.Ico t1 (t1 + A), (interference j t).toNat := by
            apply Finset.sum_le_sum
            intro t ht; rw [Finset.mem_Ico] at ht
            have ht_range : t1 ≤ t ∧ t < t2 := by
              constructor
              · exact ht.1
              · simp only [Time] at *; omega
            have h_wc := H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk
              H_job_cost_positive H_busy_interval ht_range
            -- j is not scheduled at t (since t < t1 + A ≤ job_arrival j, j hasn't arrived)
            have h_not_sched : ¬ (scheduled_at sched j t = true) := by
              intro hS
              have := H_jobs_must_arrive_to_execute j t hS
              simp only [has_arrived] at this
              simp only [Time, hA_def] at *; omega
            -- From work_conserving contrapositive: ¬scheduled → interference
            have h_intf : interference j t = true := by
              by_contra h_neg
              rw [Bool.not_eq_true] at h_neg
              exact h_not_sched (h_wc.mp (by simp [h_neg]))
            simp [h_intf]
        _ ≤ ∑ t ∈ Finset.Ico t1 (t1 + (A + F)), (interference j t).toNat := by
            apply Finset.sum_le_sum_of_subset
            intro x hx; simp only [Finset.mem_Ico] at hx ⊢; exact ⟨hx.1, Nat.lt_of_lt_of_le hx.2 (by omega)⟩
    have hNOT_COMPL_AF : ¬ completed_by job_cost sched j (t1 + (A + F)) := by
      intro hCOMPL
      apply CONTRc
      apply completion_monotonic job_cost sched j (t1 + (A + F)) (job_arrival j + R)
      · simp only [Time, hA_def] at *; omega
      · exact hCOMPL
    have hAF_lt_t2 : t1 + (A + F) < t2 := by
      rw [show A + F = A_sp + F_sp - A + A from by simp only [Time] at *; omega] at *
      simp only [Time] at *; omega
    have hIB := H_job_interference_is_bounded t1 t2 (A + F) j
      H_busy_interval hAF_lt_t2 H_j_arrives H_job_of_tsk hNOT_COMPL_AF
    calc A ≤ cumul_interference interference j t1 (t1 + (A + F)) := hCumul_ge_A
      _ ≤ interference_bound_function tsk A (A + F) := hIB
  -- FleTLIN: task_lock_in_service tsk ≤ F
  have FleTLIN : task_lock_in_service tsk ≤ F := by
    have h1 : job_arrival j - t1 ≤ interference_bound_function tsk (job_arrival j - t1)
        ((job_arrival j - t1) + F) := by simp only [hA_def] at Fact1; exact Fact1
    suffices h : (job_arrival j - t1) + task_lock_in_service tsk ≤ (job_arrival j - t1) + F from
      Nat.le_of_add_le_add_left h
    calc (job_arrival j - t1) + task_lock_in_service tsk
        ≤ interference_bound_function tsk (job_arrival j - t1) ((job_arrival j - t1) + F) +
            task_lock_in_service tsk := Nat.add_le_add_right h1 _
      _ = task_lock_in_service tsk + interference_bound_function tsk (job_arrival j - t1)
            ((job_arrival j - t1) + F) := Nat.add_comm _ _
      _ = (job_arrival j - t1) + F := hFIX2.symm
  -- NotTooOptimistic: optimism ≤ F
  have NotTooOptimistic : optimism ≤ F := by
    calc optimism = task_lock_in_service tsk - job_lock_in_service j := rfl
      _ ≤ task_lock_in_service tsk := Nat.sub_le _ _
      _ ≤ F := FleTLIN
  -- NEQf: optimism ≤ F_sp
  have NEQf : optimism ≤ F_sp := le_trans NotTooOptimistic hFleF_sp
  -- Key arithmetic: t1 + (A + F - optimism) + job_last ≤ job_arrival j + R
  have hLIS_le_cost_j := hLIS_le_cost j H_j_arrives H_job_cost_positive
  have hTLIS_bounds_j := hTLIS_bounds j H_j_arrives H_job_of_tsk
  have hCOST_le_TCOST : job_cost j ≤ task_cost tsk := by
    rw [← H_job_of_tsk]; exact H_job_cost_le_task_cost j H_j_arrives
  have CNEQ : t1 + (A + F - optimism) + job_last ≤ job_arrival j + R := by
    have h_F_bound : F + (job_cost j - task_lock_in_service tsk) ≤ R :=
      calc F + (job_cost j - task_lock_in_service tsk)
          ≤ F_sp + (task_cost tsk - task_lock_in_service tsk) :=
            Nat.add_le_add hFleF_sp (Nat.sub_le_sub_right hCOST_le_TCOST _)
        _ ≤ R := H_R_gt_Fsp
    suffices h : F - optimism + job_last ≤ R by
      rw [Nat.add_sub_assoc NotTooOptimistic]
      have h_t1A : t1 + A = job_arrival j := by
        simp only [Time, hA_def] at hGT ⊢; omega
      simp only [Time] at h h_t1A ⊢; omega
    calc F - optimism + job_last
        ≤ F - optimism + (optimism + (job_cost j - task_lock_in_service tsk)) := by
          apply Nat.add_le_add_left; simp only [hJL_def, hOPT_def]; omega
      _ = F + (job_cost j - task_lock_in_service tsk) := by
          rw [← Nat.add_assoc, Nat.sub_add_cancel NotTooOptimistic]
      _ ≤ R := h_F_bound
  -- Use j_receives_at_least_lock_in_service with delta = A + F - optimism
  have hNOT_COMPL_final : ¬ completed_by job_cost sched j (t1 + (A + F - optimism) + job_last) := by
    intro hCOMPL
    apply CONTRc
    exact completion_monotonic job_cost sched j (t1 + (A + F - optimism) + job_last)
      (job_arrival j + R) CNEQ hCOMPL
  -- Get interference bound for delta = A + F - optimism
  have hAF_sub_opt_eq : A + F - optimism + optimism = A + F :=
    Nat.sub_add_cancel (le_trans NotTooOptimistic (Nat.le_add_left F A))
  have hWorkloadBound : job_lock_in_service j + cumul_interference interference j t1 (t1 + (A + F - optimism)) ≤ A + F - optimism := by
    have hSUB : cumul_interference interference j t1 (t1 + (A + F - optimism)) ≤
        cumul_interference interference j t1 (t1 + (A + F)) := by
      simp only [cumul_interference]
      apply Finset.sum_le_sum_of_subset
      intro x hx; simp only [Finset.mem_Ico] at hx ⊢; exact ⟨hx.1, Nat.lt_of_lt_of_le hx.2 (by omega)⟩
    have hNOT_COMPL_AF : ¬ completed_by job_cost sched j (t1 + (A + F)) := by
      intro hCOMPL; apply CONTRc
      apply completion_monotonic job_cost sched j (t1 + (A + F)) (job_arrival j + R)
      · simp only [Time, hA_def] at *; omega
      · exact hCOMPL
    have hAF_lt_t2 : t1 + (A + F) < t2 := by
      simp only [Time] at *; omega
    have hIB := H_job_interference_is_bounded t1 t2 (A + F) j
      H_busy_interval hAF_lt_t2 H_j_arrives H_job_of_tsk hNOT_COMPL_AF
    dsimp only at hIB
    -- hIB: cumul_interference ≤ IBF tsk A (A+F)
    -- hFIX2: A + F = task_lock_in_service tsk + IBF tsk A (A+F)
    -- hTLIS_bounds_j: job_lock_in_service j ≤ task_lock_in_service tsk
    -- optimism = task_lock_in_service tsk - job_lock_in_service j
    simp only [Time, hOPT_def, hA_def] at *; omega
  have hESERV := j_receives_at_least_lock_in_service job_arrival job_cost job_task arr_seq sched
    tsk interference interfering_workload H_work_conserving j H_j_arrives H_job_of_tsk
    H_job_cost_positive t1 t2 H_busy_interval (job_lock_in_service j)
    hLIS_le_cost_j (A + F - optimism) hWorkloadBound
  -- Now apply job_completes_after_reaching_lock_in_service
  apply hNOT_COMPL_final
  exact job_completes_after_reaching_lock_in_service
    job_cost arr_seq sched j H_j_arrives H_completed_jobs_dont_execute
    job_lock_in_service hNONPREEMPT (t1 + (A + F - optimism)) hESERV
end FixpointIsNoLessThanArrival

section FixpointCannotBeSmallerThanArrival

variable (H_fixpoint_is_less_that_relative_arrival_of_j : A_sp + F_sp < job_arrival j - t1)

include H_busy_interval_exists H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive in
theorem relative_arrival_is_bounded :
    job_arrival j - t1 < L := by
  obtain ⟨t1', t2', h_le', h_lt', h_bound, h_busy'⟩ :=
    H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive
  have ⟨heq1, heq2⟩ := busy_interval_is_unique job_arrival job_cost sched
    interference interfering_workload j t1 t2 t1' t2' H_busy_interval h_busy'
  subst heq1; subst heq2
  obtain ⟨⟨h_le_arr, h_arr_lt, _, _⟩, _⟩ := H_busy_interval
  simp only [Time] at *; omega

include H_proper_job_lock_in_service H_proper_task_lock_in_service
  H_jobs_must_arrive_to_execute
  H_work_conserving H_busy_interval_exists H_job_interference_is_bounded
  H_busy_interval H_equivalent H_fixpoint H_small_fixpoint_solution
  H_fixpoint_is_less_that_relative_arrival_of_j H_j_arrives H_job_of_tsk H_job_cost_positive in
theorem service_of_job_ge_lock_in_service :
    job_lock_in_service j ≤ service sched j (t1 + (A_sp + F_sp)) := by
  obtain ⟨hPOS_lis, hLIS_le_cost, hNONPREEMPT⟩ := H_proper_job_lock_in_service
  obtain ⟨hTLIS_le_tcost, hTLIS_bounds⟩ := H_proper_task_lock_in_service
  have hGT := H_busy_interval.1.1
  have hLT_arr := H_busy_interval.1.2.1
  -- Step 1: Get interference bound: cumul_interference ≤ IBF tsk A (A_sp + F_sp)
  have hIB := H_job_interference_is_bounded t1 t2 (A_sp + F_sp) j
    H_busy_interval H_small_fixpoint_solution H_j_arrives H_job_of_tsk
  -- Step 2: Show ¬ completed at t1 + (A_sp + F_sp)
  have hNOT_COMPL : ¬ completed_by job_cost sched j (t1 + (A_sp + F_sp)) := by
    intro hCOMPL
    -- Since A_sp + F_sp < job_arrival j - t1, we have t1 + (A_sp+F_sp) < job_arrival j
    have hBEFORE : t1 + (A_sp + F_sp) < job_arrival j := by
      simp only [Time] at *; omega
    -- By completion_monotonic, completed at job_arrival j
    have hATARR : completed_by job_cost sched j (job_arrival j) :=
      completion_monotonic job_cost sched j (t1 + (A_sp + F_sp)) (job_arrival j)
        (le_of_lt hBEFORE) hCOMPL
    -- But service before arrival = 0
    simp only [completed_by] at hATARR
    simp only [service, service_during] at hATARR
    have hZERO : ∑ t ∈ Finset.Ico 0 (job_arrival j), service_at sched j t = 0 := by
      apply Finset.sum_eq_zero
      intro t ht; rw [Finset.mem_Ico] at ht
      simp only [service_at]
      have hNS : ¬ (scheduled_at sched j t = true) := by
        intro hS
        have := H_jobs_must_arrive_to_execute j t hS
        simp only [has_arrived] at this; simp only [Time] at *; omega
      simp only [scheduled_at] at hNS ⊢
      cases h : (sched t == some j)
      · simp [Bool.toNat]
      · exact absurd (beq_iff_eq.mp h) (by simp only [scheduled_at, beq_iff_eq] at hNS; exact hNS)
    have hPOS_unf : job_cost j > 0 := H_job_cost_positive
    simp only [Time] at *; omega
  have hIB' := hIB hNOT_COMPL
  dsimp only at hIB'
  -- Step 3: Rewrite with H_equivalent
  have hALT : job_arrival j - t1 < L := relative_arrival_is_bounded job_arrival job_cost job_task arr_seq sched tsk
    interference interfering_workload L H_busy_interval_exists j H_j_arrives H_job_of_tsk
    H_job_cost_positive t1 t2 H_busy_interval
  have hLT_L : A_sp + F_sp < L := Nat.lt_trans H_fixpoint_is_less_that_relative_arrival_of_j hALT
  rw [H_equivalent (A_sp + F_sp) hLT_L] at hIB'
  -- Step 4: Call j_receives_at_least_lock_in_service
  apply j_receives_at_least_lock_in_service job_arrival job_cost job_task arr_seq sched tsk
    interference interfering_workload H_work_conserving j H_j_arrives H_job_of_tsk
    H_job_cost_positive t1 t2 H_busy_interval (job_lock_in_service j)
    (hLIS_le_cost j H_j_arrives H_job_cost_positive)
    (A_sp + F_sp)
  -- Goal: job_lock_in_service j + cumul_interference ≤ A_sp + F_sp
  calc job_lock_in_service j + cumul_interference interference j t1 (t1 + (A_sp + F_sp))
      ≤ task_lock_in_service tsk + interference_bound_function tsk A_sp (A_sp + F_sp) := by
        apply Nat.add_le_add
        · exact hTLIS_bounds j H_j_arrives H_job_of_tsk
        · exact hIB'
    _ = A_sp + F_sp := H_fixpoint.symm
include H_proper_job_lock_in_service H_proper_task_lock_in_service
  H_jobs_must_arrive_to_execute
  H_work_conserving H_busy_interval_exists H_job_interference_is_bounded
  H_busy_interval H_equivalent H_fixpoint H_small_fixpoint_solution
  H_fixpoint_is_less_that_relative_arrival_of_j H_j_arrives H_job_of_tsk H_job_cost_positive in
theorem relative_arrival_time_is_no_less_than_fixpoint :
    False := by
  have hSERV : job_lock_in_service j ≤ service sched j (t1 + (A_sp + F_sp)) :=
    @service_of_job_ge_lock_in_service Task _ task_cost Job _
      job_arrival job_cost job_task arr_seq sched
      H_jobs_must_arrive_to_execute tsk job_lock_in_service task_lock_in_service
      H_proper_job_lock_in_service H_proper_task_lock_in_service
      interference interfering_workload H_work_conserving L H_busy_interval_exists
      interference_bound_function H_job_interference_is_bounded
      j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
      A_sp F_sp H_equivalent H_fixpoint H_small_fixpoint_solution
      H_fixpoint_is_less_that_relative_arrival_of_j
  -- t1 + (A_sp + F_sp) < job_arrival j (since A_sp + F_sp < job_arrival j - t1)
  have hLT : t1 + (A_sp + F_sp) < job_arrival j := by
    obtain ⟨⟨h_le_arr, _, _, _⟩, _⟩ := H_busy_interval
    simp only [Time] at *; omega
  -- service before arrival = 0
  have hZERO : service sched j (t1 + (A_sp + F_sp)) = 0 := by
    simp only [service, service_during]
    apply Finset.sum_eq_zero
    intro t ht; rw [Finset.mem_Ico] at ht
    simp only [service_at]
    have : ¬ (scheduled_at sched j t = true) := by
      intro hS
      have := H_jobs_must_arrive_to_execute j t hS
      simp only [has_arrived] at this; simp only [Time] at *; omega
    simp only [scheduled_at] at this ⊢
    cases h : (sched t == some j)
    · simp [Bool.toNat]
    · exact absurd (beq_iff_eq.mp h) (by simp only [beq_iff_eq] at this; exact this)
  -- lock_in ≤ 0, but lock_in > 0
  obtain ⟨hPOS, _, _⟩ := H_proper_job_lock_in_service
  have := hPOS j H_j_arrives H_job_cost_positive
  simp only [Time] at *; omega
end FixpointCannotBeSmallerThanArrival

end FixpointInsideBusyInterval

end ProofOfTheorem

include H_proper_job_lock_in_service H_proper_task_lock_in_service
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_job_cost_le_task_cost
  H_work_conserving H_busy_interval_exists H_job_interference_is_bounded H_R_is_maximum in
theorem uniprocessor_response_time_bound :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro j hARR hTSK
  by_cases hZERO : job_cost j = 0
  · -- Zero cost: trivially completed
    unfold is_response_time_bound_of_job completed_by; rw [hZERO]; exact Nat.zero_le _
  · have hPOS : job_cost_positive job_cost j := Nat.pos_of_ne_zero hZERO
    -- Get busy interval for j
    obtain ⟨t1, t2, h_le, h_lt, h_bound, h_busy⟩ :=
      H_busy_interval_exists j hARR hTSK hPOS
    -- A = job_arrival j - t1 < L
    set A := job_arrival j - t1 with hA_def
    have hA_lt_L := relative_arrival_is_bounded job_arrival job_cost job_task arr_seq sched
      tsk interference interfering_workload L H_busy_interval_exists
      j hARR hTSK hPOS t1 t2 h_busy
    -- Get representative A_sp and F_sp
    obtain ⟨A_sp, hAspLeA, hEQ, hINSP⟩ :=
      representative_exists tsk L interference_bound_function A hA_lt_L
    obtain ⟨F_sp, hFIX, hLE⟩ := H_R_is_maximum A_sp hINSP
    -- Case split on whether fixpoint is inside or outside busy interval
    by_cases hBIG : t2 ≤ t1 + (A_sp + F_sp)
    · -- Fixpoint outside busy interval
      exact @job_completed_by_arrival_plus_R_1 Task _ task_cost Job _
        job_arrival job_cost sched H_completed_jobs_dont_execute
        tsk task_lock_in_service interference interfering_workload R
        j t1 t2 h_busy A_sp F_sp hAspLeA hLE hBIG
    · -- Fixpoint inside busy interval
      push_neg at hBIG
      by_cases hBOUND : A ≤ A_sp + F_sp
      · -- A ≤ A_sp + F_sp
        exact @job_completed_by_arrival_plus_R_2 Task _ task_cost Job _
          job_arrival job_cost job_task arr_seq sched
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_job_cost_le_task_cost
          tsk job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          interference interfering_workload H_work_conserving L H_busy_interval_exists
          interference_bound_function H_job_interference_is_bounded R
          j hARR hTSK hPOS t1 t2 h_busy
          A_sp F_sp hAspLeA hEQ hINSP hFIX hLE hBIG hBOUND
      · -- A > A_sp + F_sp: contradiction
        push_neg at hBOUND
        exact absurd (@relative_arrival_time_is_no_less_than_fixpoint Task _ task_cost Job _
          job_arrival job_cost job_task arr_seq sched
          H_jobs_must_arrive_to_execute tsk job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          interference interfering_workload H_work_conserving L H_busy_interval_exists
          interference_bound_function H_job_interference_is_bounded
          j hARR hTSK hPOS t1 t2 h_busy A_sp F_sp hEQ hFIX hBIG hBOUND)
          (not_false)
end Abstract_RTA

end AbstractRTA

end Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_rta
