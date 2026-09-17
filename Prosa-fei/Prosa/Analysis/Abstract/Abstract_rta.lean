-- Translated from: ../rt-proofs/analysis/abstract/abstract_rta.v
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Abstract.Search_space
import Prosa.Analysis.Abstract.Run_to_completion

namespace Prosa.Analysis.Abstract.Abstract_rta

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Model.Processor.Platform_properties
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.Search_space
open Prosa.Analysis.Abstract.Run_to_completion
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable

private lemma t1_A_F_optimist_last_le_arrival_R_aux
    (t1 arr F trtc jrtc jc tc fsp R : Nat)
    (h1 : trtc - jrtc ≤ F) (h2 : t1 ≤ arr) (h3 : jrtc ≤ trtc)
    (h4 : jrtc ≤ jc) (h5 : jc ≤ tc) (h6 : trtc ≤ tc)
    (h7 : F ≤ fsp) (h8 : fsp + (tc - trtc) ≤ R) :
    t1 + (arr - t1 + F - (trtc - jrtc)) + (jc - jrtc) ≤ arr + R := by omega

section Abstract_RTA

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskRunToCompletionThreshold Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptable Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

attribute [local instance] pstate_instance

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable (ts : List Task)
variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (H_valid_preemption_model : valid_preemption_model arr_seq sched)

variable (H_valid_run_to_completion_threshold :
  valid_task_run_to_completion_threshold arr_seq tsk)

variable (interference : Job → instant → Bool)
variable (interfering_workload : Job → instant → duration)

variable (H_work_conserving :
  work_conserving arr_seq sched tsk interference interfering_workload)

variable (L : duration)
variable (H_busy_interval_exists :
  busy_intervals_are_bounded_by arr_seq sched tsk interference interfering_workload L)

variable (interference_bound_function : Task → duration → duration → duration)
variable (H_job_interference_is_bounded :
  job_interference_is_bounded_by arr_seq sched tsk interference interfering_workload
    interference_bound_function)

variable (R : Nat)
variable (H_R_is_maximum :
  ∀ A,
    is_in_search_space tsk L interference_bound_function A →
    ∃ F,
      A + F = task_run_to_completion_threshold tsk
              + interference_bound_function tsk A (A + F) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

section ProofOfTheorem

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost_positive j)

variable (t1 t2 : instant)
variable (H_busy_interval :
  busy_interval sched interference interfering_workload j t1 t2)

private noncomputable def A_val (j : Job) (t1 : instant) : Nat := job_arrival j - t1

variable (A_sp F_sp : duration)

variable (H_A_gt_Asp : A_sp ≤ A_val j t1)
variable (H_equivalent :
  are_equivalent_at_values_less_than
    (interference_bound_function tsk (A_val j t1))
    (interference_bound_function tsk A_sp) L)
variable (H_Asp_is_in_search_space :
  is_in_search_space tsk L interference_bound_function A_sp)
variable (H_Asp_Fsp_fixpoint :
  A_sp + F_sp = task_run_to_completion_threshold tsk
    + interference_bound_function tsk A_sp (A_sp + F_sp))
variable (H_R_gt_Fsp :
  F_sp + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

section FixpointOutsideBusyInterval

variable (H_big_fixpoint_solution : t2 ≤ t1 + (A_sp + F_sp))

include H_busy_interval H_A_gt_Asp H_R_gt_Fsp H_big_fixpoint_solution in
theorem t2_le_arrival_plus_R :
    t2 ≤ job_arrival j + R := by
  have h1 : A_sp ≤ job_arrival j - t1 := H_A_gt_Asp
  have h2 : t2 ≤ t1 + (A_sp + F_sp) := H_big_fixpoint_solution
  have h3 : F_sp + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R := H_R_gt_Fsp
  have h4 : t1 ≤ job_arrival j := H_busy_interval.1.1.1
  unfold duration instant at *
  omega

include H_busy_interval H_A_gt_Asp H_R_gt_Fsp H_big_fixpoint_solution
  H_completed_jobs_dont_execute H_work_conserving H_j_arrives H_job_of_tsk
  H_job_cost_positive H_arrival_times_are_consistent H_valid_job_cost in
theorem job_completed_by_arrival_plus_R_1 :
    completed_by sched j (job_arrival j + R) := by
  have h_le : t2 ≤ job_arrival j + R :=
    t2_le_arrival_plus_R sched tsk interference interfering_workload R j t1 t2
      H_busy_interval A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_big_fixpoint_solution
  have h_compl : completed_by sched j t2 :=
    job_completes_within_busy_interval
      arr_seq H_arrival_times_are_consistent sched H_valid_job_cost
      tsk interference interfering_workload H_work_conserving
      j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
  exact completion_monotonic sched j t2 (job_arrival j + R) h_le h_compl

end FixpointOutsideBusyInterval

section FixpointInsideBusyInterval

variable (H_small_fixpoint_solution : t1 + (A_sp + F_sp) < t2)

section FixpointIsNoLessThanArrival

variable (H_fixpoint_is_no_less_than_relative_arrival_of_j : A_val j t1 ≤ A_sp + F_sp)

section ProofByContradiction

variable (F : duration)
variable (H_Asp_Fsp_eq_A_F : A_sp + F_sp = A_val j t1 + F)
variable (H_F_le_Fsp : F ≤ F_sp)
variable (H_A_F_fixpoint :
  A_val j t1 + F = task_run_to_completion_threshold tsk
    + interference_bound_function tsk (A_val j t1) (A_val j t1 + F))

variable (H_j_not_completed : ¬ completed_by sched j (job_arrival j + R))

private noncomputable def job_last_val (j : Job) : Nat :=
  job_cost j - job_run_to_completion_threshold j

private noncomputable def optimism_val (tsk : Task) (j : Job) : Nat :=
  task_run_to_completion_threshold tsk - job_run_to_completion_threshold j

-- Standalone include for ALL variables needed by theorems in this section
include H_busy_interval H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive
  H_arrival_times_are_consistent H_valid_run_to_completion_threshold
  H_valid_preemption_model H_completed_jobs_dont_execute H_valid_job_cost
  H_jobs_must_arrive_to_execute H_job_interference_is_bounded
  H_Asp_Fsp_eq_A_F H_A_F_fixpoint H_j_not_completed H_small_fixpoint_solution
  H_A_gt_Asp H_R_gt_Fsp H_F_le_Fsp

theorem j_is_completed_by_t1_A_F_optimist_last :
    completed_by sched j
      (t1 + (A_val j t1 + F - optimism_val tsk j) + job_last_val j) := by
  -- Use j_receives_at_least_run_to_completion_threshold with
  --   progress_of_job := job_run_to_completion_threshold j
  --   delta := A_val j t1 + F - optimism_val tsk j
  have h_t1_le : t1 ≤ job_arrival j := H_busy_interval.1.1.1
  have h_asp_eq : A_sp + F_sp = A_val j t1 + F := H_Asp_Fsp_eq_A_F
  have h_jrtc_le_trtc : job_run_to_completion_threshold j ≤ task_run_to_completion_threshold tsk :=
    H_valid_run_to_completion_threshold.2 j H_j_arrives H_job_of_tsk
  -- Show the workload bound:
  --   job_rtc + cumul_interference j t1 (t1 + delta) ≤ delta
  -- where delta = (A + F) - optimism
  have h_workload_bounded :
      job_run_to_completion_threshold j +
        cumul_interference interference j t1 (t1 + (A_val j t1 + F - optimism_val tsk j)) ≤
        A_val j t1 + F - optimism_val tsk j := by
    -- Key: (A+F) - opt = (task_rtc + IBF) - (task_rtc - job_rtc) = job_rtc + IBF
    -- So goal becomes: job_rtc + cumul ≤ job_rtc + IBF, i.e., cumul ≤ IBF
    -- cumul monotonicity: cumul(..., t1 + (A+F-opt)) ≤ cumul(..., t1 + (A+F))
    -- IBF bound: cumul(..., t1 + (A+F)) ≤ IBF
    have h_not_compl : ¬ completed_by sched j (t1 + (A_val j t1 + F)) := by
      intro h_compl
      apply H_j_not_completed
      have h_le : t1 + (A_val j t1 + F) ≤ job_arrival j + R := by
        have : A_val j t1 = job_arrival j - t1 := rfl
        have := H_F_le_Fsp; have := H_R_gt_Fsp
        unfold duration instant at *; omega
      exact completion_monotonic sched j _ _ h_le h_compl
    have h_lt_t2 : t1 + (A_val j t1 + F) < t2 := by
      rw [← h_asp_eq]; exact H_small_fixpoint_solution
    -- cumul_interference over [t1, t1+(A+F-opt)) ≤ cumul over [t1, t1+(A+F))
    have h_opt_le_AF : optimism_val tsk j ≤ A_val j t1 + F := by
      -- optimism = task_rtc - job_rtc ≤ task_rtc ≤ task_rtc + IBF = A + F
      have h_fix := H_A_F_fixpoint
      unfold optimism_val A_val at *
      unfold duration instant at *; omega
    have h_cumul_mono : cumul_interference interference j t1 (t1 + (A_val j t1 + F - optimism_val tsk j)) ≤
        cumul_interference interference j t1 (t1 + (A_val j t1 + F)) := by
      unfold cumul_interference
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.Ico_subset_Ico_right
        exact Nat.add_le_add_left (Nat.sub_le _ _) t1
      · intros; exact Nat.zero_le _
    -- cumul over [t1, t1+(A+F)) ≤ IBF
    have h_ibf := H_job_interference_is_bounded t1 t2 (A_val j t1 + F) j
      H_j_arrives H_job_of_tsk H_busy_interval h_lt_t2 h_not_compl
    -- From fixpoint: A+F = task_rtc + IBF
    -- So (A+F) - opt = (task_rtc + IBF) - (task_rtc - job_rtc) = job_rtc + IBF
    -- Need: job_rtc + cumul ≤ (A+F) - opt = job_rtc + IBF
    -- i.e., cumul ≤ IBF
    calc job_run_to_completion_threshold j +
          cumul_interference interference j t1 (t1 + (A_val j t1 + F - optimism_val tsk j))
        ≤ job_run_to_completion_threshold j +
          cumul_interference interference j t1 (t1 + (A_val j t1 + F)) :=
          Nat.add_le_add_left h_cumul_mono _
      _ ≤ job_run_to_completion_threshold j +
          interference_bound_function tsk (A_val j t1) (A_val j t1 + F) :=
          Nat.add_le_add_left h_ibf _
      _ ≤ A_val j t1 + F - optimism_val tsk j := by
          -- From fixpoint: A+F = task_rtc + IBF, so job_rtc + IBF = (A+F) - opt
          have h_fix := H_A_F_fixpoint
          unfold A_val optimism_val at *
          unfold duration instant at *; omega
  -- Apply j_receives_at_least_run_to_completion_threshold
  have h_serv :=
    @j_receives_at_least_run_to_completion_threshold
      Task _ Job _ _ _ _ _
      arr_seq H_arrival_times_are_consistent sched H_valid_job_cost
      tsk interference interfering_workload H_work_conserving
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval
      (job_run_to_completion_threshold j)
      (job_run_to_completion_threshold_le_job_cost j)
      (A_val j t1 + F - optimism_val tsk j)
      h_workload_bounded
  -- Apply job_completes_after_reaching_run_to_completion_threshold
  have h_compl :=
    @job_completes_after_reaching_run_to_completion_threshold
      Task _ Job _ _ _ _ _
      arr_seq H_arrival_times_are_consistent sched H_valid_job_cost
      tsk interference interfering_workload H_work_conserving
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval
      H_completed_jobs_dont_execute H_valid_preemption_model
      (t1 + (A_val j t1 + F - optimism_val tsk j)) h_serv
  -- h_compl : completed_by sched j (t1 + delta + (job_cost j - job_rtc j))
  -- This is exactly the goal (with job_last_val = job_cost - job_rtc)
  unfold job_last_val
  exact h_compl

-- AuxiliaryInequalities (no separate section to avoid premature universalization)

theorem relative_arrival_le_interference_bound :
    A_val j t1 ≤ interference_bound_function tsk (A_val j t1) (A_val j t1 + F) := by
  have h_t1_le : t1 ≤ job_arrival j := H_busy_interval.1.1.1
  have h_asp_eq : A_sp + F_sp = A_val j t1 + F := H_Asp_Fsp_eq_A_F
  have h_lt_t2 : t1 + (A_val j t1 + F) < t2 := by
    rw [← h_asp_eq]; exact H_small_fixpoint_solution
  have h_not_compl : ¬ completed_by sched j (t1 + (A_val j t1 + F)) := by
    intro h_compl
    apply H_j_not_completed
    have h_le : t1 + (A_val j t1 + F) ≤ job_arrival j + R := by
      have : A_val j t1 = job_arrival j - t1 := rfl
      have := H_F_le_Fsp; have := H_R_gt_Fsp
      unfold duration instant at *; omega
    exact completion_monotonic sched j _ _ h_le h_compl
  -- Each interference j x = true for x ∈ [t1, t1 + A)
  have h_intf_true : ∀ x ∈ Finset.Ico t1 (t1 + A_val j t1), (interference j x).toNat ≥ 1 := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    suffices interference j x = true by rw [this]; norm_num
    by_contra h_not_true
    have h_x_lt_t2 : x < t2 := by
      have : A_val j t1 = job_arrival j - t1 := rfl
      unfold duration instant at *; omega
    have h_wc := H_work_conserving j t1 t2 x H_j_arrives H_job_of_tsk H_job_cost_positive
      H_busy_interval ⟨hx.1, h_x_lt_t2⟩
    have h_sched : scheduled_at sched j x = true := h_wc.mp h_not_true
    have h_arr := H_jobs_must_arrive_to_execute j x h_sched
    have h_x_lt_arr : x < job_arrival j := by
      have : A_val j t1 = job_arrival j - t1 := rfl
      unfold duration instant at *; omega
    exact absurd h_arr (not_le.mpr h_x_lt_arr)
  -- A ≤ Σ x in [t1, t1+A), interference
  have h_A_le_sum : A_val j t1 ≤ ∑ x ∈ Finset.Ico t1 (t1 + A_val j t1), (interference j x).toNat := by
    have h_card : (Finset.Ico t1 (t1 + A_val j t1)).card = A_val j t1 := by
      rw [Nat.card_Ico]; unfold duration instant A_val at *; omega
    have h_one_le := Finset.sum_le_sum h_intf_true
    rw [Finset.sum_const, smul_eq_mul, mul_one] at h_one_le
    rw [h_card] at h_one_le
    exact h_one_le
  -- Subset sum monotonicity + IBF bound
  have h_subset : Finset.Ico t1 (t1 + A_val j t1) ⊆ Finset.Ico t1 (t1 + (A_val j t1 + F)) :=
    Finset.Ico_subset_Ico_right (Nat.add_le_add_left (Nat.le_add_right _ F) t1)
  have h_A_le_cumul : A_val j t1 ≤ cumul_interference interference j t1 (t1 + (A_val j t1 + F)) := by
    unfold cumul_interference
    exact Nat.le_trans h_A_le_sum
      (Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => Nat.zero_le _))
  exact Nat.le_trans h_A_le_cumul
    (H_job_interference_is_bounded t1 t2 (A_val j t1 + F) j
      H_j_arrives H_job_of_tsk H_busy_interval h_lt_t2 h_not_compl)

theorem tsk_run_to_completion_threshold_le_Fsp :
    task_run_to_completion_threshold tsk ≤ F_sp := by
  have h1 := @relative_arrival_le_interference_bound
      Task _ _ Job _ _ _ _ _
      arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_valid_job_cost tsk H_valid_preemption_model
      H_valid_run_to_completion_threshold interference interfering_workload
      H_work_conserving interference_bound_function H_job_interference_is_bounded
      R j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
      A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_small_fixpoint_solution F
      H_Asp_Fsp_eq_A_F H_F_le_Fsp H_A_F_fixpoint H_j_not_completed
  -- h1 : A_val j t1 ≤ IBF
  have h2 := H_A_F_fixpoint
  -- h2 : A_val j t1 + F = task_rtc + IBF
  -- From h1 and h2: task_rtc ≤ F
  have h_rtc_le_F : task_run_to_completion_threshold tsk ≤ F := by
    have h4 := Nat.add_le_add_left h1 (k := task_run_to_completion_threshold tsk)
    rw [h2.symm] at h4
    rw [Nat.add_comm (task_run_to_completion_threshold tsk)] at h4
    exact Nat.le_of_add_le_add_left h4
  exact Nat.le_trans h_rtc_le_F H_F_le_Fsp

theorem optimism_le_F :
    optimism_val tsk j ≤ F := by
  have h1 := @relative_arrival_le_interference_bound
      Task _ _ Job _ _ _ _ _
      arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_valid_job_cost tsk H_valid_preemption_model
      H_valid_run_to_completion_threshold interference interfering_workload
      H_work_conserving interference_bound_function H_job_interference_is_bounded
      R j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
      A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_small_fixpoint_solution F
      H_Asp_Fsp_eq_A_F H_F_le_Fsp H_A_F_fixpoint H_j_not_completed
  have h2 := H_A_F_fixpoint
  -- task_rtc ≤ F (same as in tsk_run_to_completion_threshold_le_Fsp)
  have h_rtc_le_F : task_run_to_completion_threshold tsk ≤ F := by
    have h4 := Nat.add_le_add_left h1 (k := task_run_to_completion_threshold tsk)
    rw [h2.symm] at h4
    rw [Nat.add_comm (task_run_to_completion_threshold tsk)] at h4
    exact Nat.le_of_add_le_add_left h4
  -- optimism = task_rtc - job_rtc ≤ task_rtc ≤ F
  change task_run_to_completion_threshold tsk - job_run_to_completion_threshold j ≤ F
  exact Nat.le_trans (Nat.sub_le _ _) h_rtc_le_F

-- end AuxiliaryInequalities

theorem t1_A_F_optimist_last_le_arrival_R :
    t1 + (A_val j t1 + F - optimism_val tsk j) + job_last_val j ≤ job_arrival j + R := by
  have h_opt_le_F := @optimism_le_F
    Task _ _ Job _ _ _ _ _
    arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_valid_job_cost tsk H_valid_preemption_model
    H_valid_run_to_completion_threshold interference interfering_workload
    H_work_conserving interference_bound_function H_job_interference_is_bounded
    R j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
    A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_small_fixpoint_solution F
    H_Asp_Fsp_eq_A_F H_F_le_Fsp H_A_F_fixpoint H_j_not_completed
  unfold optimism_val at h_opt_le_F
  unfold A_val optimism_val job_last_val
  have h_jcost_le : job_cost j ≤ task_cost tsk := by
    have h := H_valid_job_cost j H_j_arrives
    unfold valid_job_cost at h; rw [H_job_of_tsk] at h; exact h
  exact t1_A_F_optimist_last_le_arrival_R_aux
    t1 (job_arrival j) F
    (task_run_to_completion_threshold tsk) (job_run_to_completion_threshold j)
    (job_cost j) (task_cost tsk) F_sp R
    h_opt_le_F
    H_busy_interval.1.1.1
    (H_valid_run_to_completion_threshold.2 j H_j_arrives H_job_of_tsk)
    (job_run_to_completion_threshold_le_job_cost j)
    h_jcost_le
    H_valid_run_to_completion_threshold.1
    H_F_le_Fsp
    H_R_gt_Fsp

theorem j_is_completed_earlier_contradiction :
    False := by
  have h_compl := @j_is_completed_by_t1_A_F_optimist_last
    Task _ _ Job _ _ _ _ _
    arr_seq H_arrival_times_are_consistent sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost
    tsk H_valid_preemption_model H_valid_run_to_completion_threshold
    interference interfering_workload H_work_conserving interference_bound_function
    H_job_interference_is_bounded R j H_j_arrives H_job_of_tsk H_job_cost_positive
    t1 t2 H_busy_interval A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_small_fixpoint_solution
    F H_Asp_Fsp_eq_A_F H_F_le_Fsp H_A_F_fixpoint H_j_not_completed
  have h_le := @t1_A_F_optimist_last_le_arrival_R
    Task _ _ Job _ _ _ _ _
    arr_seq H_arrival_times_are_consistent sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost
    tsk H_valid_preemption_model H_valid_run_to_completion_threshold
    interference interfering_workload H_work_conserving interference_bound_function
    H_job_interference_is_bounded R j H_j_arrives H_job_of_tsk H_job_cost_positive
    t1 t2 H_busy_interval A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_small_fixpoint_solution
    F H_Asp_Fsp_eq_A_F H_F_le_Fsp H_A_F_fixpoint H_j_not_completed
  have h_done := completion_monotonic sched j _ _ h_le h_compl
  exact H_j_not_completed h_done

end ProofByContradiction

include H_busy_interval H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive
  H_arrival_times_are_consistent H_valid_run_to_completion_threshold
  H_valid_preemption_model H_completed_jobs_dont_execute H_valid_job_cost
  H_jobs_must_arrive_to_execute H_job_interference_is_bounded
  H_small_fixpoint_solution H_A_gt_Asp H_R_gt_Fsp
  H_Asp_Fsp_fixpoint H_equivalent H_Asp_is_in_search_space
  H_busy_interval_exists H_fixpoint_is_no_less_than_relative_arrival_of_j in
theorem job_completed_by_arrival_plus_R_2 :
    completed_by sched j (job_arrival j + R) := by
  by_contra h_not_compl
  -- Get A_sp + F_sp < L
  have h_t1_le : t1 ≤ job_arrival j := H_busy_interval.1.1.1
  have h_aspfsp_lt_L : A_sp + F_sp < L := by
    have ⟨t1', t2', _, h_bound, h_bi'⟩ :=
      H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive
    have ⟨h_eq1, h_eq2⟩ := busy_interval_is_unique sched interference interfering_workload
      j t1 t2 t1' t2' H_busy_interval h_bi'
    subst h_eq1; subst h_eq2
    unfold duration instant at *; omega
  -- Use solution_for_A_exists with wrapped IBF
  let ibf_wrapped := fun (tsk : Task) (A R : duration) =>
    task_run_to_completion_threshold tsk + interference_bound_function tsk A R
  have h_fix_wrapped : A_sp + F_sp = ibf_wrapped tsk A_sp (A_sp + F_sp) := H_Asp_Fsp_fixpoint
  have h_equiv_wrapped : are_equivalent_at_values_less_than
      (ibf_wrapped tsk (A_val j t1)) (ibf_wrapped tsk A_sp) L := by
    intro x hx
    show task_run_to_completion_threshold tsk + interference_bound_function tsk (A_val j t1) x =
        task_run_to_completion_threshold tsk + interference_bound_function tsk A_sp x
    congr 1
    exact H_equivalent x hx
  have h_bounds : A_sp ≤ A_val j t1 ∧ A_val j t1 ≤ A_sp + F_sp :=
    ⟨H_A_gt_Asp, H_fixpoint_is_no_less_than_relative_arrival_of_j⟩
  obtain ⟨F, h_eq, h_F_le, h_fix⟩ := solution_for_A_exists
    tsk L ibf_wrapped A_sp F_sp (A_val j t1)
    h_aspfsp_lt_L h_fix_wrapped h_bounds h_equiv_wrapped
  -- h_eq : A_sp + F_sp = A_val j t1 + F
  -- h_F_le : F ≤ F_sp
  -- h_fix : A_val j t1 + F = ibf_wrapped tsk (A_val j t1) (A_val j t1 + F)
  --       = task_rtc + IBF tsk (A_val j t1) (A_val j t1 + F)
  exact absurd (@j_is_completed_earlier_contradiction
      Task _ _ Job _ _ _ _ _
      arr_seq H_arrival_times_are_consistent sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost
      tsk H_valid_preemption_model H_valid_run_to_completion_threshold
      interference interfering_workload H_work_conserving interference_bound_function
      H_job_interference_is_bounded R j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval A_sp F_sp H_A_gt_Asp H_R_gt_Fsp H_small_fixpoint_solution
      F h_eq h_F_le h_fix h_not_compl) id

end FixpointIsNoLessThanArrival

section FixpointCannotBeSmallerThanArrival

variable (H_fixpoint_is_less_that_relative_arrival_of_j : A_sp + F_sp < A_val j t1)

include H_busy_interval H_busy_interval_exists H_j_arrives H_job_of_tsk
  H_job_cost_positive H_fixpoint_is_less_that_relative_arrival_of_j in
theorem relative_arrival_is_bounded :
    A_val j t1 < L := by
  have ⟨t1', t2', _, h_bound, h_bi'⟩ :=
    H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive
  have ⟨h_eq1, h_eq2⟩ := busy_interval_is_unique sched interference interfering_workload
    j t1 t2 t1' t2' H_busy_interval h_bi'
  subst h_eq1; subst h_eq2
  obtain ⟨⟨⟨h_t1_le, h_arr_lt⟩, _, _⟩, _⟩ := H_busy_interval
  have h_falt := H_fixpoint_is_less_that_relative_arrival_of_j
  change A_sp + F_sp < job_arrival j - t1 at h_falt
  have : A_val j t1 = job_arrival j - t1 := rfl
  unfold duration instant at *
  omega

include H_busy_interval H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive
  H_arrival_times_are_consistent H_valid_run_to_completion_threshold
  H_valid_preemption_model H_completed_jobs_dont_execute H_valid_job_cost
  H_jobs_must_arrive_to_execute H_job_interference_is_bounded
  H_small_fixpoint_solution H_Asp_Fsp_fixpoint H_fixpoint_is_less_that_relative_arrival_of_j
  H_equivalent H_busy_interval_exists in
theorem service_of_job_ge_run_to_completion_threshold :
    service sched j (t1 + (A_sp + F_sp)) ≥ job_run_to_completion_threshold j := by
  have h_t1_le : t1 ≤ job_arrival j := H_busy_interval.1.1.1
  have h_falt := H_fixpoint_is_less_that_relative_arrival_of_j
  -- ¬ completed_by at t1 + (A_sp + F_sp): j hasn't arrived yet
  have h_not_compl : ¬ completed_by sched j (t1 + (A_sp + F_sp)) := by
    intro h_compl
    have h_le_arr : t1 + (A_sp + F_sp) ≤ job_arrival j := by
      have : A_val j t1 = job_arrival j - t1 := rfl
      unfold duration instant at *; omega
    have h_compl_arr := completion_monotonic sched j _ _ h_le_arr h_compl
    have h_serv_zero := no_service_before_arrival sched j H_jobs_must_arrive_to_execute
      (job_arrival j) (le_refl _)
    unfold completed_by at h_compl_arr
    rw [h_serv_zero] at h_compl_arr
    exact absurd H_job_cost_positive (Nat.not_lt.mpr h_compl_arr)
  -- IBF bound: cumul ≤ IBF tsk A (A_sp + F_sp)
  have h_ibf := H_job_interference_is_bounded t1 t2 (A_sp + F_sp) j
    H_j_arrives H_job_of_tsk H_busy_interval H_small_fixpoint_solution h_not_compl
  -- Use H_equivalent to replace IBF tsk A with IBF tsk A_sp
  have h_A_lt_L : A_val j t1 < L := by
    have ⟨t1', t2', _, h_bound, h_bi'⟩ :=
      H_busy_interval_exists j H_j_arrives H_job_of_tsk H_job_cost_positive
    have ⟨h_eq1, h_eq2⟩ := busy_interval_is_unique sched interference interfering_workload
      j t1 t2 t1' t2' H_busy_interval h_bi'
    subst h_eq1; subst h_eq2
    obtain ⟨⟨⟨_, h_arr_lt⟩, _, _⟩, _⟩ := H_busy_interval
    have : A_val j t1 = job_arrival j - t1 := rfl
    unfold duration instant at *; omega
  have h_aspfsp_lt_L : A_sp + F_sp < L := Nat.lt_trans h_falt h_A_lt_L
  have h_equiv := H_equivalent (A_sp + F_sp) h_aspfsp_lt_L
  -- h_equiv : IBF tsk (A_val j t1) (A_sp + F_sp) = IBF tsk A_sp (A_sp + F_sp)
  simp only [] at h_ibf  -- unfold let offset
  rw [show job_arrival j - t1 = A_val j t1 from rfl] at h_ibf
  rw [h_equiv] at h_ibf
  -- Workload bound: job_rtc + cumul ≤ A_sp + F_sp
  have h_jrtc_le_trtc : job_run_to_completion_threshold j ≤ task_run_to_completion_threshold tsk :=
    H_valid_run_to_completion_threshold.2 j H_j_arrives H_job_of_tsk
  have h_workload : job_run_to_completion_threshold j +
      cumul_interference interference j t1 (t1 + (A_sp + F_sp)) ≤ A_sp + F_sp := by
    calc job_run_to_completion_threshold j +
          cumul_interference interference j t1 (t1 + (A_sp + F_sp))
        ≤ task_run_to_completion_threshold tsk +
          interference_bound_function tsk A_sp (A_sp + F_sp) :=
          Nat.add_le_add h_jrtc_le_trtc h_ibf
      _ = A_sp + F_sp := H_Asp_Fsp_fixpoint.symm
  exact @j_receives_at_least_run_to_completion_threshold
    Task _ Job _ _ _ _ _
    arr_seq H_arrival_times_are_consistent sched H_valid_job_cost
    tsk interference interfering_workload H_work_conserving
    j H_j_arrives H_job_of_tsk H_job_cost_positive
    t1 t2 H_busy_interval
    (job_run_to_completion_threshold j)
    (job_run_to_completion_threshold_le_job_cost j)
    (A_sp + F_sp)
    h_workload

include H_busy_interval H_work_conserving H_j_arrives H_job_of_tsk H_job_cost_positive
  H_arrival_times_are_consistent H_valid_run_to_completion_threshold
  H_valid_preemption_model H_completed_jobs_dont_execute H_valid_job_cost
  H_jobs_must_arrive_to_execute H_job_interference_is_bounded
  H_small_fixpoint_solution H_Asp_Fsp_fixpoint H_fixpoint_is_less_that_relative_arrival_of_j
  H_busy_interval_exists H_equivalent H_A_gt_Asp in
theorem relative_arrival_time_is_no_less_than_fixpoint :
    False := by
  have h_serv := @service_of_job_ge_run_to_completion_threshold
    Task _ _ Job _ _ _ _ _
    arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_valid_job_cost tsk H_valid_preemption_model
    H_valid_run_to_completion_threshold interference interfering_workload
    H_work_conserving L H_busy_interval_exists interference_bound_function
    H_job_interference_is_bounded
    j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval
    A_sp F_sp H_equivalent H_Asp_Fsp_fixpoint
    H_small_fixpoint_solution
    H_fixpoint_is_less_that_relative_arrival_of_j
  -- h_serv : service sched j (t1 + (A_sp + F_sp)) ≥ job_rtc j
  -- But t1 + (A_sp + F_sp) ≤ job_arrival j, so service = 0
  have h_le_arr : t1 + (A_sp + F_sp) ≤ job_arrival j := by
    have := H_fixpoint_is_less_that_relative_arrival_of_j
    have : A_val j t1 = job_arrival j - t1 := rfl
    have : t1 ≤ job_arrival j := H_busy_interval.1.1.1
    unfold duration instant at *; omega
  have h_serv_zero := no_service_before_arrival sched j H_jobs_must_arrive_to_execute
    (t1 + (A_sp + F_sp)) h_le_arr
  rw [h_serv_zero] at h_serv
  -- h_serv : 0 ≥ job_rtc j, but job_rtc > 0
  have h_pos := job_run_to_completion_threshold_positive arr_seq sched
    H_valid_preemption_model j H_j_arrives H_job_cost_positive
  exact absurd h_pos (not_lt.mpr h_serv)

end FixpointCannotBeSmallerThanArrival

end FixpointInsideBusyInterval

end ProofOfTheorem

include H_arrival_times_are_consistent H_valid_job_cost H_valid_preemption_model
  H_valid_run_to_completion_threshold H_work_conserving H_busy_interval_exists
  H_job_interference_is_bounded H_R_is_maximum H_completed_jobs_dont_execute
  H_jobs_must_arrive_to_execute in
theorem uniprocessor_response_time_bound :
    task_response_time_bound arr_seq sched tsk R := by
  intro j h_arrives h_job_of_tsk
  unfold job_response_time_bound
  by_cases h_pos : job_cost_positive j
  · -- job_cost > 0: get busy interval
    obtain ⟨t1, t2, _, h_bound, h_bi⟩ :=
      H_busy_interval_exists j h_arrives h_job_of_tsk h_pos
    have h_t1_le : t1 ≤ job_arrival j := h_bi.1.1.1
    have h_arr_lt_t2 : job_arrival j < t2 := h_bi.1.1.2
    have h_A_lt_L : A_val j t1 < L := by
      have : A_val j t1 = job_arrival j - t1 := rfl
      unfold duration instant at *; omega
    obtain ⟨A_sp, h_asp_le, h_equiv, h_insp⟩ :=
      representative_exists tsk L interference_bound_function (A_val j t1) h_A_lt_L
    obtain ⟨F_sp, h_fix, h_R_ge⟩ := H_R_is_maximum A_sp h_insp
    by_cases h_big : t2 ≤ t1 + (A_sp + F_sp)
    · -- Big fixpoint
      exact job_completed_by_arrival_plus_R_1
        arr_seq H_arrival_times_are_consistent sched H_completed_jobs_dont_execute
        H_valid_job_cost tsk interference interfering_workload H_work_conserving R
        j h_arrives h_job_of_tsk h_pos t1 t2 h_bi A_sp F_sp h_asp_le h_R_ge h_big
    · push_neg at h_big
      by_cases h_bound2 : A_val j t1 ≤ A_sp + F_sp
      · -- Fixpoint ≥ arrival
        exact job_completed_by_arrival_plus_R_2
          arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_valid_job_cost tsk H_valid_preemption_model
          H_valid_run_to_completion_threshold interference interfering_workload
          H_work_conserving L H_busy_interval_exists interference_bound_function
          H_job_interference_is_bounded R j h_arrives h_job_of_tsk h_pos t1 t2 h_bi
          A_sp F_sp h_asp_le h_equiv h_insp h_fix h_R_ge h_big h_bound2
      · -- Fixpoint < arrival: contradiction
        push_neg at h_bound2
        exact absurd (relative_arrival_time_is_no_less_than_fixpoint
          arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_valid_job_cost tsk H_valid_preemption_model
          H_valid_run_to_completion_threshold interference interfering_workload
          H_work_conserving L H_busy_interval_exists interference_bound_function
          H_job_interference_is_bounded j h_arrives h_job_of_tsk h_pos t1 t2 h_bi
          A_sp F_sp h_asp_le h_equiv h_fix h_big h_bound2) id
  · -- job_cost = 0
    unfold job_cost_positive at h_pos; push_neg at h_pos
    have h_zero : job_cost j = 0 := Nat.le_zero.mp h_pos
    show completed_by sched j (job_arrival j + R)
    unfold completed_by; rw [h_zero]; exact Nat.zero_le _

end Abstract_RTA
