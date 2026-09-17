-- Translated from: ../rt-proofs/analysis/facts/busy_interval/carry_in.v
import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Definitions.Carry_in
import Prosa.Analysis.Facts.Busy_interval.Busy_interval
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic

namespace Prosa.Analysis.Facts.Busy_interval.Carry_in

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.Work_conserving
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Analysis.Definitions.Carry_in
open Prosa.Analysis.Definitions.Busy_interval
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Facts.Busy_interval.Busy_interval
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Service_of_jobs

set_option linter.dupNamespace false

section ExistsNoCarryIn

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable [JLFP_policy Job]

attribute [local instance] JLFP_to_JLDP

theorem no_carry_in_implies_quiet_time :
    ∀ (j : Job) (t : instant),
      no_carry_in arr_seq sched t →
      quiet_time arr_seq sched j t := by
  intro j t FQT j_hp ARR HP BEF
  exact FQT j_hp ARR BEF

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_arrival_sequence_is_a_set : arrival_sequence_uniq arr_seq)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set in
theorem idle_instant_implies_no_carry_in_at_t :
    ∀ (t : instant),
      is_idle sched t →
      no_carry_in arr_seq sched t := by
  intro t IDLE j ARR HA
  by_contra NCOMPL
  have HARR : has_arrived j t := Nat.le_of_lt HA
  have HIDLE : sched t = none := IDLE
  have NSCHED : scheduled_at sched j t = false := by
    simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def]
    rw [HIDLE]; simp
  have BACK : backlogged sched j t = true := by
    simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
    refine ⟨?_, NSCHED⟩
    show job_ready sched j t = true
    simp only [JobReady.job_ready,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
    exact ⟨HARR, NCOMPL⟩
  obtain ⟨j', SCHED⟩ := H_work_conserving j t ARR BACK
  simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def] at SCHED
  rw [HIDLE] at SCHED; simp at SCHED

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set in
theorem idle_instant_implies_no_carry_in_at_t_pl_1 :
    ∀ (t : instant),
      is_idle sched t →
      no_carry_in arr_seq sched (t + 1) := by
  intro t IDLE j ARR HA
  by_contra NCOMPL
  have HARR : has_arrived j t := by
    simp only [has_arrived, arrived_before] at *; exact Nat.lt_add_one_iff.mp HA
  have NCOMPL_t : ¬ completed_by sched j t := by
    intro hc; exact NCOMPL (completion_monotonic sched j t (t + 1) (Nat.le_succ t) hc)
  have HIDLE : sched t = none := IDLE
  have NSCHED : scheduled_at sched j t = false := by
    simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def]
    rw [HIDLE]; simp
  have BACK : backlogged sched j t = true := by
    simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
    refine ⟨?_, NSCHED⟩
    show job_ready sched j t = true
    simp only [JobReady.job_ready,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
    exact ⟨HARR, NCOMPL_t⟩
  obtain ⟨j', SCHED⟩ := H_work_conserving j t ARR BACK
  simp only [scheduled_at, Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_in_def] at SCHED
  rw [HIDLE] at SCHED; simp at SCHED

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))

section ProcessorIsNotTooBusy

theorem no_carry_in_at_the_beginning :
    no_carry_in arr_seq sched 0 := by
  intro s ARR AB
  exfalso
  exact Nat.not_lt_zero _ AB

section ProcessorIsNotTooBusyInduction

variable (Δ : duration)
variable (H_delta_positive : Δ > 0)
variable (H_workload_is_bounded :
  ∀ t, workload_of_jobs (fun _ => true) (arrivals_between arr_seq t (t + Δ)) ≤ Δ)

variable (t : duration)
variable (H_no_carry_in : no_carry_in arr_seq sched t)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_no_carry_in in
theorem total_service_is_bounded_by_Δ :
    service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) ≤ Δ := by
  have h := service_of_jobs_le_length_of_interval' arr_seq H_arrival_times_are_consistent
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute (fun _ => true) (arrivals_between arr_seq 0 (t + Δ))
    (Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq arr_seq H_arrival_times_are_consistent
      H_arrival_sequence_is_a_set 0 (t + Δ))
    t (t + Δ)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_no_carry_in in
theorem low_total_service_implies_existence_of_time_with_no_carry_in :
    service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) < Δ →
    ∃ δ, δ < Δ ∧ no_carry_in arr_seq sched (t + 1 + δ) := by
  intro LT
  -- Rewrite Δ as (t + Δ) - t to apply the idle time lemma
  have LT' : service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) < (t + Δ) - t := by
    simp only [Nat.add_sub_cancel_left]; exact LT
  obtain ⟨t_idle, hle, hlt, IDLE⟩ := low_service_implies_existence_of_idle_time arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t (t + Δ) LT'
  by_cases ht_eq : t_idle = t
  · -- t_idle = t: use δ = 0
    subst ht_eq
    refine ⟨0, H_delta_positive, ?_⟩
    rw [Nat.add_zero]
    exact idle_instant_implies_no_carry_in_at_t_pl_1 arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set _ IDLE
  · -- t_idle > t: use δ = t_idle - t - 1
    have hlt_t : t < t_idle := Nat.lt_of_le_of_ne hle (Ne.symm ht_eq)
    have ht_idle_eq : ∃ γ, t_idle = t + γ := ⟨t_idle - t, by exact (Nat.add_sub_cancel' (Nat.le_of_lt hlt_t)).symm⟩
    obtain ⟨γ, rfl⟩ := ht_idle_eq
    have hγ_pos : γ ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by intro h; subst h; exact absurd rfl ht_eq)
    have hγ_lt_Δ : γ < Δ := Nat.lt_of_add_lt_add_left hlt
    exists γ - 1
    constructor
    · exact Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.one_pos hγ_pos) Nat.one_pos) (Nat.le_of_lt hγ_lt_Δ)
    · have heq : t + 1 + (γ - 1) = t + γ := by
        have h1 := Nat.add_sub_cancel' hγ_pos
        simp only [instant, duration] at *
        rw [Nat.add_assoc, h1]
      rw [heq]
      exact idle_instant_implies_no_carry_in_at_t arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set (t + γ) IDLE

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_no_carry_in in
theorem completion_of_all_jobs_implies_no_carry_in :
    service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) = Δ →
    no_carry_in arr_seq sched (t + Δ) := by
  intro EQserv
  -- Old jobs completed at t
  have COMPL_old : ∀ j', j' ∈ arrivals_between arr_seq 0 t → (fun (_ : Job) => true) j' = true →
      completed_by sched j' t := by
    intro j' ARR' _
    apply H_no_carry_in
    · exact Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
        arr_seq H_arrival_times_are_consistent j' 0 t ARR'
    · exact (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between
        arr_seq H_arrival_times_are_consistent j' 0 t ARR').2
  have EQ_old := Prosa.Analysis.Facts.Model.Service_of_jobs.all_jobs_have_completed_impl_workload_eq_service
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (fun (_ : Job) => true) 0 t t COMPL_old
  -- Split workload at t
  have h_wl_split := Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_cat
    arr_seq t 0 (t + Δ) (fun (_ : Job) => true) ⟨Nat.zero_le _, Nat.le_add_right _ _⟩
  -- Split service at scheduling interval t
  have h_sched_split := Prosa.Analysis.Facts.Model.Service_of_jobs.service_of_jobs_cat_scheduling_interval
    arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute (fun (_ : Job) => true) 0 (t + Δ) t
    (Nat.zero_le _) (Nat.le_add_right _ _)
  -- Split arrival interval for service in [t, t+Δ)
  have h_arr_split := Prosa.Analysis.Facts.Model.Service_of_jobs.service_of_jobs_cat_arrival_interval
    arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute (fun (_ : Job) => true) 0 (t + Δ) t
    (Nat.zero_le _) (Nat.le_add_right _ _)
  -- Show total workload = total service for [0, t+Δ)
  have h_wl_bound := H_workload_is_bounded t
  have h_svc_sum : service_of_jobs sched (fun (_ : Job) => true) (arrivals_between arr_seq 0 t) t (t + Δ)
      + service_of_jobs sched (fun (_ : Job) => true) (arrivals_between arr_seq t (t + Δ)) t (t + Δ) = Δ := by
    rw [← h_arr_split]; exact EQserv
  have h_total_eq : workload_of_jobs (fun (_ : Job) => true) (arrivals_between arr_seq 0 (t + Δ)) =
      service_of_jobs sched (fun (_ : Job) => true) (arrivals_between arr_seq 0 (t + Δ)) 0 (t + Δ) := by
    apply le_antisymm
    · -- workload ≤ service: linear arithmetic on the decompositions
      rw [h_wl_split, EQ_old, h_sched_split, Nat.add_assoc]
      apply Nat.add_le_add_left
      rw [h_svc_sum]
      exact h_wl_bound
    · -- service ≤ workload
      exact Prosa.Analysis.Facts.Model.Service_of_jobs.service_of_jobs_le_workload
        arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute (fun (_ : Job) => true)
        (arrivals_between arr_seq 0 (t + Δ))
        Prosa.Analysis.Facts.Model.Ideal_schedule.ideal_proc_model_provides_unit_service 0 (t + Δ)
  -- Conclude
  intro s ARR_s BEF_s
  have hIN_s := Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
    arr_seq H_arrival_times_are_consistent s 0 (t + Δ) ARR_s ⟨Nat.zero_le _, BEF_s⟩
  exact Prosa.Analysis.Facts.Model.Service_of_jobs.workload_eq_service_impl_all_jobs_have_completed
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (fun (_ : Job) => true) 0 (t + Δ) (t + Δ) h_total_eq s hIN_s rfl

end ProcessorIsNotTooBusyInduction

variable (Δ : duration)
variable (H_delta_positive : Δ > 0)
variable (H_workload_is_bounded :
  ∀ t, workload_of_jobs (fun _ => true) (arrivals_between arr_seq t (t + Δ)) ≤ Δ)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_delta_positive H_workload_is_bounded in
theorem processor_is_not_too_busy :
    ∀ t, ∃ δ, δ < Δ ∧ no_carry_in arr_seq sched (t + δ) := by
  intro t
  induction t with
  | zero =>
    exact ⟨0, H_delta_positive, by rw [Nat.zero_add]; exact no_carry_in_at_the_beginning arr_seq sched⟩
  | succ n ih =>
    obtain ⟨δ, hLT, hFQT⟩ := ih
    by_cases hδ_pos : δ > 0
    · -- δ > 0: use δ - 1
      obtain ⟨k, rfl⟩ : ∃ k, δ = k + 1 := ⟨δ - 1, (Nat.succ_pred_eq_of_pos hδ_pos).symm⟩
      refine ⟨k, Nat.lt_of_succ_lt hLT, ?_⟩
      have : n + 1 + k = n + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [this]; exact hFQT
    · -- δ = 0: n is no_carry_in
      simp only [Nat.not_lt, Nat.le_zero] at hδ_pos
      subst hδ_pos; rw [Nat.add_zero] at hFQT
      -- Check total service in [n, n+Δ)
      have h_le := total_service_is_bounded_by_Δ arr_seq H_arrival_times_are_consistent sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set
        H_priority_is_reflexive Δ H_delta_positive H_workload_is_bounded n hFQT
      rcases Nat.eq_or_lt_of_le h_le with h_eq | h_lt
      · -- service = Δ: all jobs completed, n+Δ is no_carry_in
        obtain ⟨k, rfl⟩ : ∃ k, Δ = k + 1 := ⟨Δ - 1, (Nat.succ_pred_eq_of_pos H_delta_positive).symm⟩
        refine ⟨k, Nat.lt_succ_of_le le_rfl, ?_⟩
        have heq : n + 1 + k = n + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]
        rw [heq]
        exact completion_of_all_jobs_implies_no_carry_in arr_seq H_arrival_times_are_consistent
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set
          H_priority_is_reflexive (k + 1) (Nat.succ_pos k) H_workload_is_bounded n hFQT h_eq
      · -- service < Δ: idle time exists
        obtain ⟨δ', hLT', hNCI⟩ := low_total_service_implies_existence_of_time_with_no_carry_in
          arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
          H_arrival_sequence_is_a_set H_priority_is_reflexive Δ H_delta_positive H_workload_is_bounded
          n hFQT h_lt
        exact ⟨δ', hLT', by rw [show n + 1 + δ' = n + 1 + δ' from rfl]; exact hNCI⟩

end ProcessorIsNotTooBusy

variable (Δ : duration)
variable (H_delta_positive : Δ > 0)
variable (H_workload_is_bounded :
  ∀ t, workload_of_jobs (fun _ => true) (arrivals_between arr_seq t (t + Δ)) ≤ Δ)

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))

variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)
variable (H_job_cost_positive : job_cost_positive j)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_priority_is_reflexive H_from_arrival_sequence H_job_cost_positive in
theorem exists_busy_interval_from_total_workload_bound :
    ∃ t1 t2,
      t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
      t2 ≤ t1 + Δ ∧
      busy_interval arr_seq sched j t1 t2 := by
  -- Step 1: j is pending at arrival
  have hPEND : pending sched j (job_arrival j) :=
    job_pending_at_arrival sched j H_job_cost_positive H_jobs_must_arrive_to_execute
  -- Step 2: Get busy interval prefix at job_arrival j
  obtain ⟨t1, hPrefix, hGE1_out, _⟩ := exists_busy_interval_prefix arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    j H_from_arrival_sequence H_job_cost_positive H_work_conserving
    H_arrival_sequence_is_a_set H_priority_is_reflexive (job_arrival j) hPEND
  obtain ⟨hLT_prefix, hQT1, hNQT_prefix, hLE1, hLTarr⟩ := hPrefix
  -- Step 3: Get no_carry_in via processor_is_not_too_busy at (t1 + 1)
  obtain ⟨δ, hδLT, hNCI⟩ := processor_is_not_too_busy arr_seq H_arrival_times_are_consistent
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_arrival_sequence_is_a_set
    H_priority_is_reflexive Δ H_delta_positive H_workload_is_bounded (t1 + 1)
  -- Convert to quiet_time
  have hQT_far : quiet_time arr_seq sched j (t1 + 1 + δ) :=
    no_carry_in_implies_quiet_time arr_seq sched j (t1 + 1 + δ) hNCI
  -- Step 4: Find minimum n such that quiet_time_dec (t1 + 1 + n) = true
  have hEXn : ∃ n, quiet_time_dec arr_seq sched j (t1 + 1 + n) = true :=
    ⟨δ, (quiet_time_P arr_seq H_arrival_times_are_consistent sched j (t1 + 1 + δ)).mpr hQT_far⟩
  set n₀ := Nat.find hEXn with hn₀_def
  set t2 := t1 + 1 + n₀ with ht2_def
  -- Step 5: Properties of t2
  have hQT2_dec := Nat.find_spec hEXn
  have hQUIET_t2 : quiet_time arr_seq sched j t2 :=
    (quiet_time_P arr_seq H_arrival_times_are_consistent sched j t2).mp hQT2_dec
  have hN0_le_δ : n₀ ≤ δ := Nat.find_min' hEXn
    ((quiet_time_P arr_seq H_arrival_times_are_consistent sched j (t1 + 1 + δ)).mpr hQT_far)
  have hGT : t1 < t2 := by
    calc t1 < t1 + 1 := Nat.lt_succ_of_le le_rfl
      _ ≤ t1 + 1 + n₀ := Nat.le_add_right _ _
      _ = t2 := ht2_def.symm
  have hLE2 : t2 ≤ t1 + Δ := by
    rw [ht2_def, Nat.add_assoc, Nat.add_comm 1 n₀]
    exact Nat.add_le_add_left (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hN0_le_δ hδLT)) t1
  -- Step 6: No quiet time in (t1, t2)
  have hNQT2 : ∀ t, t1 < t ∧ t < t2 → ¬quiet_time arr_seq sched j t := by
    intro t ⟨hgt, hlt⟩ hqt
    have hlt' : t < t1 + 1 + n₀ := ht2_def ▸ hlt
    have hge : t1 + 1 ≤ t := hgt
    have hlt_n : t - (t1 + 1) < n₀ := Nat.sub_lt_left_of_lt_add hge hlt'
    have hNeg := Nat.find_min hEXn hlt_n
    have h_eq : t1 + 1 + (t - (t1 + 1)) = t := Nat.add_sub_cancel' hge
    rw [h_eq] at hNeg
    exact hNeg ((quiet_time_P arr_seq H_arrival_times_are_consistent sched j t).mpr hqt)
  -- Step 7: Show job_arrival j < t2
  have hARR_lt : job_arrival j < t2 := by
    by_contra hle
    push_neg at hle
    exact hNQT_prefix t2 ⟨hGT, Nat.lt_succ_of_le hle⟩ hQUIET_t2
  -- Step 8: Assemble
  exact ⟨t1, t2, hLE1, hARR_lt, hLE2,
    ⟨⟨hGT, hQT1, hNQT2, hLE1, hARR_lt⟩, hQUIET_t2⟩⟩

end ExistsNoCarryIn

end Prosa.Analysis.Facts.Busy_interval.Carry_in
