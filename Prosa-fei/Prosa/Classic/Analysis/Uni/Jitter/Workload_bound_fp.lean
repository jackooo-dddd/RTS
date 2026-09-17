-- Translated from: ../rt-proofs/classic/analysis/uni/jitter/workload_bound_fp.v
import Prosa.Classic.Util.Div_mod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Arrival.Jitter.Arrival_bounds
import Prosa.Classic.Model.Arrival.Jitter.Task_arrival
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Priority
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Div_mod
open Prosa.Classic.Model.Arrival.Jitter.Arrival_bounds
open Prosa.Classic.Model.Arrival.Jitter.Task_arrival

namespace WorkloadBoundFP

section SingleTask

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)
  variable (task_period : Task → Time)
  variable (task_jitter : Task → Time)

  variable (tsk : Task)
  variable (delta : Time)

  def max_jobs := div_ceil (delta + task_jitter tsk) (task_period tsk)

  def task_workload_bound_FP := max_jobs task_period task_jitter tsk delta * task_cost tsk

end SingleTask

section AllTasks

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)
  variable (task_period : Task → Time)
  variable (task_jitter : Task → Time)

  variable (higher_eq_priority : FP_policy Task)

  variable (ts : List Task)

  variable (tsk : Task)

  variable (delta : Time)

  def total_workload_bound_fp :=
    (ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk)).map
      (fun tsk_other => task_workload_bound_FP task_cost task_period task_jitter tsk_other delta) |>.sum

end AllTasks

section BasicLemmas

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)
  variable (task_period : Task → Time)
  variable (task_deadline : Task → Time)
  variable (task_jitter : Task → Time)

  variable (higher_eq_priority : FP_policy Task)

  variable (ts : List Task)

  variable (tsk : Task)
  variable (H_tsk_in_ts : tsk ∈ ts)

  section NoSmallerThanCost

    variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)

    variable (H_cost_positive : task_cost tsk > 0)
    variable (H_period_positive : task_period tsk > 0)

    include H_tsk_in_ts H_priority_is_reflexive H_cost_positive H_period_positive

    theorem total_workload_bound_fp_ge_cost :
        total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk (task_cost tsk) ≥ task_cost tsk := by
      unfold total_workload_bound_fp
      have h_tsk_in_filtered : tsk ∈ ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk) := by
        rw [List.mem_filter]
        exact ⟨H_tsk_in_ts, H_priority_is_reflexive tsk⟩
      have h_term_ge : task_workload_bound_FP task_cost task_period task_jitter tsk (task_cost tsk) ≥ task_cost tsk := by
        unfold task_workload_bound_FP
        have h_ceil : max_jobs task_period task_jitter tsk (task_cost tsk) ≥ 1 := by
          apply ceil_neq0
          · exact Nat.lt_of_lt_of_le H_cost_positive (Nat.le_add_right _ _)
          · exact H_period_positive
        calc task_cost tsk = 1 * task_cost tsk := by ring
          _ ≤ max_jobs task_period task_jitter tsk (task_cost tsk) * task_cost tsk := by
              exact Nat.mul_le_mul_right _ h_ceil
      have h_in_mapped : task_workload_bound_FP task_cost task_period task_jitter tsk (task_cost tsk) ∈
          (ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk)).map
            (fun tsk_other => task_workload_bound_FP task_cost task_period task_jitter tsk_other (task_cost tsk)) := by
        apply List.mem_map_of_mem
        exact h_tsk_in_filtered
      apply le_trans h_term_ge
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_in_mapped

  end NoSmallerThanCost

  section NonDecreasing

    variable (H_period_positive : ∀ tsk, tsk ∈ ts → task_period tsk > 0)

    include H_period_positive

    theorem total_workload_bound_fp_non_decreasing :
        ∀ delta1 delta2,
          delta1 ≤ delta2 →
          total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk delta1 ≤
          total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk delta2 := by
      intro d1 d2 LE
      unfold total_workload_bound_fp task_workload_bound_FP
      set filtered := ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk)
      suffices h : ∀ (l : List Task),
          (∀ t, t ∈ l → t ∈ ts) →
          (l.map (fun tsk_other => max_jobs task_period task_jitter tsk_other d1 * task_cost tsk_other)).sum ≤
          (l.map (fun tsk_other => max_jobs task_period task_jitter tsk_other d2 * task_cost tsk_other)).sum by
        apply h
        intro t ht
        exact List.mem_of_mem_filter ht
      intro l
      induction l with
      | nil => intro _; simp
      | cons hd tl ih =>
        intro hmem
        simp only [List.map_cons, List.sum_cons]
        apply Nat.add_le_add
        · apply Nat.mul_le_mul_right
          unfold max_jobs
          apply leq_divceil2r
          · exact H_period_positive hd (hmem hd (List.Mem.head tl))
          · exact Nat.add_le_add_right LE _
        · exact ih (fun t ht => hmem t (List.Mem.tail hd ht))

  end NonDecreasing

end BasicLemmas

section ProofWorkloadBound

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)
  variable (task_period : Task → Time)
  variable (task_jitter : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_jitter : Job → Time)
  variable (job_task : Job → Task)

  variable (ts : List Task)

  variable (H_positive_periods : ∀ tsk, tsk ∈ ts → task_period tsk > 0)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)

  variable (H_all_jobs_from_taskset :
    ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

  variable (H_job_cost_le_task_cost :
    ∀ j,
      arrives_in arr_seq j →
      job_cost j ≤ task_cost (job_task j))

  variable (H_job_jitter_le_task_jitter :
    ∀ j,
      arrives_in arr_seq j →
      job_jitter j ≤ task_jitter (job_task j))

  variable (H_sporadic_arrivals :
    sporadic_task_model task_period job_arrival job_task arr_seq)

  variable (tsk : Task)
  variable (H_tsk_in_ts : tsk ∈ ts)

  variable (higher_eq_priority : FP_policy Task)

  variable (R : Time)
  variable (H_fixed_point : R = total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk R)

  include H_positive_periods H_arrival_times_are_consistent H_arrival_sequence_is_a_set
          H_all_jobs_from_taskset H_job_cost_le_task_cost H_job_jitter_le_task_jitter
          H_sporadic_arrivals H_tsk_in_ts H_fixed_point

  theorem fp_workload_bound_holds :
      ∀ t,
        workload_of_higher_or_equal_priority_tasks job_cost job_task
          (actual_arrivals_between job_arrival job_jitter arr_seq t (t + R))
          higher_eq_priority tsk ≤ R := by
    intro t
    conv_rhs => rw [H_fixed_point]
    unfold workload_of_higher_or_equal_priority_tasks workload_of_jobs
    unfold total_workload_bound_fp task_workload_bound_FP
    set l := actual_arrivals_between job_arrival job_jitter arr_seq t (t + R)
    set hep := higher_eq_priority
    set filtered_ts := ts.filter (fun tsk_other => hep tsk_other tsk)
    -- Step 1: Exchange sum structure (group jobs by task)
    set filtered := l.filter (fun j => hep (job_task j) tsk) with filtered_def
    have exchange : ∀ (jobs : List Job) (groups : List Task),
        (∀ j0, j0 ∈ jobs → job_task j0 ∈ groups) →
        (jobs.map job_cost).sum ≤
        (groups.map (fun g =>
          ((jobs.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
      intro jobs groups h_cover
      induction jobs with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons]
        have h_cover_tl := fun j0 hj0 => h_cover j0 (List.mem_cons_of_mem hd hj0)
        have h_rhs :
            (groups.map (fun g =>
              (((hd :: tl).filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum =
            (groups.map (fun g =>
              (if decide (job_task hd = g) then job_cost hd else 0) +
              ((tl.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
          apply congr_arg List.sum
          apply List.map_congr_left; intro g _
          simp only [List.filter_cons]
          cases h : decide (job_task hd = g) <;> simp
        rw [h_rhs, List.sum_map_add]
        have h_hd : job_cost hd ≤
            (groups.map (fun g => if decide (job_task hd = g) then job_cost hd else 0)).sum := by
          have h_mem := h_cover hd List.mem_cons_self
          have h_in : (fun g => if decide (job_task hd = g) then job_cost hd else (0 : ℕ)) (job_task hd) ∈
              groups.map (fun g => if decide (job_task hd = g) then job_cost hd else 0) :=
            List.mem_map_of_mem h_mem
          simp only [decide_true] at h_in
          exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_in
        exact Nat.add_le_add h_hd (ih h_cover_tl)
    -- Inline arrival count bound
    have arrival_count_bound : ∀ tsk' : Task, tsk' ∈ ts →
        (l.filter (fun j0 => decide (job_task j0 = tsk'))).length ≤
        max_jobs task_period task_jitter tsk' R := by
      intro tsk' htsk'
      unfold max_jobs
      -- The filter gives us num_actual_arrivals_of_task
      have h_eq : (l.filter (fun j0 => decide (job_task j0 = tsk'))).length =
          num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk' t (t + R) := by
        simp only [num_actual_arrivals_of_task, actual_arrivals_of_task_between, l]
        congr 1
      rw [h_eq]
      have BOUND := sporadic_task_with_jitter_arrival_bound task_period task_jitter
        job_arrival job_jitter job_task arr_seq H_arrival_times_are_consistent
        H_arrival_sequence_is_a_set H_job_jitter_le_task_jitter H_sporadic_arrivals
        t (t + R) tsk' (H_positive_periods tsk' htsk')
      -- BOUND : num_actual_arrivals_of_task ... ≤ div_ceil ((t + R) + task_jitter tsk' - t) (task_period tsk')
      -- Goal: ... ≤ div_ceil (R + task_jitter tsk') (task_period tsk')
      convert BOUND using 2
      omega
    have per_task_bound : ∀ tsk', tsk' ∈ ts →
        ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum ≤
        max_jobs task_period task_jitter tsk' R * task_cost tsk' := by
      intro tsk' htsk'
      set fl := l.filter (fun j0 => decide (job_task j0 = tsk'))
      have h_cost_bound : (fl.map job_cost).sum ≤ task_cost tsk' * fl.length := by
        have h_bound : ∀ x ∈ fl.map job_cost, x ≤ task_cost tsk' := by
          intro x hx; rw [List.mem_map] at hx
          obtain ⟨j0, hj0_mem, rfl⟩ := hx
          simp only [fl, List.mem_filter, decide_eq_true_eq] at hj0_mem
          have hj0_arrives := in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq
            H_arrival_times_are_consistent j0 t (t + R) hj0_mem.1
          have := H_job_cost_le_task_cost j0 hj0_arrives
          rw [hj0_mem.2] at this; exact this
        have h1 := List.sum_le_card_nsmul (fl.map job_cost) (task_cost tsk') h_bound
        rw [smul_eq_mul, List.length_map] at h1
        rw [Nat.mul_comm]; exact h1
      have h_count_bound : fl.length ≤ max_jobs task_period task_jitter tsk' R :=
        arrival_count_bound tsk' htsk'
      calc (fl.map job_cost).sum
          ≤ task_cost tsk' * fl.length := h_cost_bound
        _ ≤ task_cost tsk' * max_jobs task_period task_jitter tsk' R :=
            Nat.mul_le_mul_left _ h_count_bound
        _ = max_jobs task_period task_jitter tsk' R * task_cost tsk' := Nat.mul_comm _ _
    have h_exch : (filtered.map job_cost).sum ≤
        (filtered_ts.map (fun g =>
          ((filtered.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
      apply exchange
      intro j0 hj0
      simp only [filtered, List.mem_filter] at hj0
      simp only [filtered_ts, List.mem_filter]
      constructor
      · exact H_all_jobs_from_taskset j0
          (in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq
            H_arrival_times_are_consistent j0 t (t + R) hj0.1)
      · exact hj0.2
    apply le_trans h_exch
    apply List.sum_le_sum
    intro tsk' htsk'
    have htsk'_in_ts := List.mem_of_mem_filter htsk'
    calc ((filtered.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum
        ≤ ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum :=
          (List.Sublist.map job_cost (List.Sublist.filter _ List.filter_sublist)).sum_le_sum
            (fun _ _ => Nat.zero_le _)
      _ ≤ max_jobs task_period task_jitter tsk' R * task_cost tsk' :=
          per_task_bound tsk' htsk'_in_ts

end ProofWorkloadBound

end WorkloadBoundFP

end Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp
