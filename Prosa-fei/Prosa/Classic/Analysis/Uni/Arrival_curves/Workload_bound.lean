-- Translated from: ../rt-proofs/classic/analysis/uni/arrival_curves/workload_bound.v
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Priority

namespace MaxArrivalsWorkloadBound

section Lemmas

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

variable (higher_eq_priority : FP_policy Task)

section RequestBoundFunction

variable (max_arrivals : Task → Time → Nat)

section SingleTask

variable (tsk : Task)
variable (delta : Time)

def task_request_bound_function := task_cost tsk * max_arrivals tsk delta

end SingleTask

section AllTasks

variable (ts : List Task)
variable (tsk : Task)
variable (delta : Time)

def total_request_bound_function :=
  (ts.map (fun tsk' => task_request_bound_function task_cost max_arrivals tsk' delta)).sum

def total_hep_request_bound_function_FP :=
  ((ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk)).map
    (fun tsk_other => task_request_bound_function task_cost max_arrivals tsk_other delta)).sum

def total_ohep_request_bound_function_FP :=
  ((ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk && decide (tsk_other ≠ tsk))).map
    (fun tsk_other => task_request_bound_function task_cost max_arrivals tsk_other delta)).sum

end AllTasks

end RequestBoundFunction

section ProofWorkloadBound

variable (ts : List Task)
variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (H_job_cost_le_task_cost :
  ∀ j, arrives_in arr_seq j →
    job_cost j ≤ task_cost (job_task j))

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (max_arrivals : Task → Time → Nat)
variable (H_is_arrival_bound :
  is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

section WorkloadIsBoundedByRBF

variable (t : Time)
variable (delta : Time)

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_job_cost_le_task_cost
  H_is_arrival_bound H_j_arrives H_job_of_tsk H_tsk_in_ts in
theorem task_workload_le_task_rbf :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta))
      (fun j_other => decide (job_task j_other = job_task j)) ≤
    task_request_bound_function task_cost max_arrivals tsk delta := by
  unfold workload_of_jobs task_request_bound_function
  have hj_eq : (fun j_other => decide (job_task j_other = job_task j)) =
    (fun j_other => decide (job_task j_other = tsk)) := by
    ext x; simp [H_job_of_tsk]
  rw [hj_eq]
  set filtered := (jobs_arrived_between arr_seq t (t + delta)).filter
    (fun j_other => decide (job_task j_other = tsk))
  calc (filtered.map job_cost).sum
      ≤ task_cost tsk * filtered.length := by
        have h_bound : ∀ x ∈ filtered.map job_cost, x ≤ task_cost tsk := by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨j0, hj0_mem, rfl⟩ := hx
          simp only [filtered, List.mem_filter, decide_eq_true_eq] at hj0_mem
          obtain ⟨hj0_in, hj0_task⟩ := hj0_mem
          have hj0_arrives : arrives_in arr_seq j0 :=
            in_arrivals_implies_arrived job_arrival arr_seq
              H_arrival_times_are_consistent j0 t (t + delta) hj0_in
          have := H_job_cost_le_task_cost j0 hj0_arrives
          rw [hj0_task] at this; exact this
        have h1 := List.sum_le_card_nsmul (filtered.map job_cost) (task_cost tsk) h_bound
        rw [smul_eq_mul, List.length_map] at h1
        rw [Nat.mul_comm]; exact h1
    _ ≤ task_cost tsk * max_arrivals tsk delta := by
        apply Nat.mul_le_mul_left
        have h_tsk_bound := H_is_arrival_bound tsk H_tsk_in_ts
        have h_bound := h_tsk_bound t (t + delta) (Nat.le_add_right t delta)
        simp at h_bound; exact h_bound

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_job_cost_le_task_cost
  H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
theorem total_workload_le_total_rbf :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta))
      (fun j_other => FP_to_JLFP job_task higher_eq_priority j_other j &&
        decide (job_task j_other ≠ job_task j)) ≤
    total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk delta := by
  unfold workload_of_jobs total_ohep_request_bound_function_FP task_request_bound_function
  set l := jobs_arrived_between arr_seq t (t + delta)
  have h_pred_eq : (fun j_other => FP_to_JLFP job_task higher_eq_priority j_other j &&
      decide (job_task j_other ≠ job_task j)) =
    (fun j_other => higher_eq_priority (job_task j_other) tsk && decide (job_task j_other ≠ tsk)) := by
    ext x; simp [FP_to_JLFP, H_job_of_tsk]
  rw [h_pred_eq]
  set filtered := l.filter (fun j_other =>
    higher_eq_priority (job_task j_other) tsk && decide (job_task j_other ≠ tsk))
  set task_filtered := ts.filter (fun tsk_other =>
    higher_eq_priority tsk_other tsk && decide (tsk_other ≠ tsk))
  -- Exchange: group filtered jobs by task
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
      rw [h_rhs]
      rw [List.sum_map_add]
      have h_hd : job_cost hd ≤
          (groups.map (fun g => if decide (job_task hd = g) then job_cost hd else 0)).sum := by
        have h_mem := h_cover hd List.mem_cons_self
        have h_in : (fun g => if decide (job_task hd = g) then job_cost hd else (0 : ℕ)) (job_task hd) ∈
            groups.map (fun g => if decide (job_task hd = g) then job_cost hd else 0) :=
          List.mem_map_of_mem h_mem
        simp only [decide_true] at h_in
        exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_in
      exact Nat.add_le_add h_hd (ih h_cover_tl)
  -- Per-task bound
  have per_task_bound : ∀ tsk', tsk' ∈ ts →
      ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum ≤
      task_cost tsk' * max_arrivals tsk' delta := by
    intro tsk' htsk'
    set fl := l.filter (fun j0 => decide (job_task j0 = tsk'))
    calc (fl.map job_cost).sum
        ≤ task_cost tsk' * fl.length := by
          have h_bound : ∀ x ∈ fl.map job_cost, x ≤ task_cost tsk' := by
            intro x hx; rw [List.mem_map] at hx
            obtain ⟨j0, hj0_mem, rfl⟩ := hx
            simp only [fl, List.mem_filter, decide_eq_true_eq] at hj0_mem
            have hj0_arrives := in_arrivals_implies_arrived job_arrival arr_seq
              H_arrival_times_are_consistent j0 t (t + delta) hj0_mem.1
            have := H_job_cost_le_task_cost j0 hj0_arrives
            rw [hj0_mem.2] at this; exact this
          have h1 := List.sum_le_card_nsmul (fl.map job_cost) (task_cost tsk') h_bound
          rw [smul_eq_mul, List.length_map] at h1
          rw [Nat.mul_comm]; exact h1
      _ ≤ task_cost tsk' * max_arrivals tsk' delta := by
          apply Nat.mul_le_mul_left
          have h_bound := (H_is_arrival_bound tsk' htsk') t (t + delta) (Nat.le_add_right t delta)
          simp at h_bound; exact h_bound
  -- Main proof
  have h_exch : (filtered.map job_cost).sum ≤
      (task_filtered.map (fun g =>
        ((filtered.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
    apply exchange
    intro j0 hj0
    simp only [filtered, List.mem_filter] at hj0
    simp only [task_filtered, List.mem_filter]
    exact ⟨H_all_jobs_from_taskset j0
      (in_arrivals_implies_arrived job_arrival arr_seq
        H_arrival_times_are_consistent j0 t (t + delta) hj0.1), hj0.2⟩
  apply le_trans h_exch
  apply List.sum_le_sum
  intro tsk' htsk'
  calc ((filtered.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum
      ≤ ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum :=
        (List.Sublist.map job_cost (List.Sublist.filter _ List.filter_sublist)).sum_le_sum
          (fun _ _ => Nat.zero_le _)
    _ ≤ task_cost tsk' * max_arrivals tsk' delta :=
        per_task_bound tsk' (List.mem_of_mem_filter htsk')

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_job_cost_le_task_cost
  H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
theorem total_workload_le_total_rbf' :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta))
      (fun j_other => FP_to_JLFP job_task higher_eq_priority j_other j) ≤
    total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk delta := by
  unfold workload_of_jobs total_hep_request_bound_function_FP task_request_bound_function
  set l := jobs_arrived_between arr_seq t (t + delta)
  have h_pred_eq : (fun j_other => FP_to_JLFP job_task higher_eq_priority j_other j) =
    (fun j_other => higher_eq_priority (job_task j_other) tsk) := by
    ext x; simp [FP_to_JLFP, H_job_of_tsk]
  rw [h_pred_eq]
  set filtered := l.filter (fun j_other => higher_eq_priority (job_task j_other) tsk)
  set task_filtered := ts.filter (fun tsk_other => higher_eq_priority tsk_other tsk)
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
  have per_task_bound : ∀ tsk', tsk' ∈ ts →
      ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum ≤
      task_cost tsk' * max_arrivals tsk' delta := by
    intro tsk' htsk'
    set fl := l.filter (fun j0 => decide (job_task j0 = tsk'))
    calc (fl.map job_cost).sum
        ≤ task_cost tsk' * fl.length := by
          have h_bound : ∀ x ∈ fl.map job_cost, x ≤ task_cost tsk' := by
            intro x hx; rw [List.mem_map] at hx
            obtain ⟨j0, hj0_mem, rfl⟩ := hx
            simp only [fl, List.mem_filter, decide_eq_true_eq] at hj0_mem
            have hj0_arrives := in_arrivals_implies_arrived job_arrival arr_seq
              H_arrival_times_are_consistent j0 t (t + delta) hj0_mem.1
            have := H_job_cost_le_task_cost j0 hj0_arrives
            rw [hj0_mem.2] at this; exact this
          have h1 := List.sum_le_card_nsmul (fl.map job_cost) (task_cost tsk') h_bound
          rw [smul_eq_mul, List.length_map] at h1
          rw [Nat.mul_comm]; exact h1
      _ ≤ task_cost tsk' * max_arrivals tsk' delta := by
          apply Nat.mul_le_mul_left
          have h_bound := (H_is_arrival_bound tsk' htsk') t (t + delta) (Nat.le_add_right t delta)
          simp at h_bound; exact h_bound
  have h_exch : (filtered.map job_cost).sum ≤
      (task_filtered.map (fun g =>
        ((filtered.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
    apply exchange
    intro j0 hj0
    simp only [filtered, List.mem_filter] at hj0
    simp only [task_filtered, List.mem_filter]
    exact ⟨H_all_jobs_from_taskset j0
      (in_arrivals_implies_arrived job_arrival arr_seq
        H_arrival_times_are_consistent j0 t (t + delta) hj0.1), hj0.2⟩
  apply le_trans h_exch
  apply List.sum_le_sum
  intro tsk' htsk'
  calc ((filtered.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum
      ≤ ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum :=
        (List.Sublist.map job_cost (List.Sublist.filter _ List.filter_sublist)).sum_le_sum
          (fun _ _ => Nat.zero_le _)
    _ ≤ task_cost tsk' * max_arrivals tsk' delta :=
        per_task_bound tsk' (List.mem_of_mem_filter htsk')

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_job_cost_le_task_cost
  H_all_jobs_from_taskset H_is_arrival_bound in
theorem total_workload_le_total_rbf'' :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta))
      (fun _ => true) ≤
    total_request_bound_function task_cost max_arrivals ts delta := by
  unfold workload_of_jobs total_request_bound_function task_request_bound_function
  set l := jobs_arrived_between arr_seq t (t + delta)
  simp only [List.filter_true]
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
  have per_task_bound : ∀ tsk', tsk' ∈ ts →
      ((l.filter (fun j0 => decide (job_task j0 = tsk'))).map job_cost).sum ≤
      task_cost tsk' * max_arrivals tsk' delta := by
    intro tsk' htsk'
    set fl := l.filter (fun j0 => decide (job_task j0 = tsk'))
    calc (fl.map job_cost).sum
        ≤ task_cost tsk' * fl.length := by
          have h_bound : ∀ x ∈ fl.map job_cost, x ≤ task_cost tsk' := by
            intro x hx; rw [List.mem_map] at hx
            obtain ⟨j0, hj0_mem, rfl⟩ := hx
            simp only [fl, List.mem_filter, decide_eq_true_eq] at hj0_mem
            have hj0_arrives := in_arrivals_implies_arrived job_arrival arr_seq
              H_arrival_times_are_consistent j0 t (t + delta) hj0_mem.1
            have := H_job_cost_le_task_cost j0 hj0_arrives
            rw [hj0_mem.2] at this; exact this
          have h1 := List.sum_le_card_nsmul (fl.map job_cost) (task_cost tsk') h_bound
          rw [smul_eq_mul, List.length_map] at h1
          rw [Nat.mul_comm]; exact h1
      _ ≤ task_cost tsk' * max_arrivals tsk' delta := by
          apply Nat.mul_le_mul_left
          have h_bound := (H_is_arrival_bound tsk' htsk') t (t + delta) (Nat.le_add_right t delta)
          simp at h_bound; exact h_bound
  have h_exch : (l.map job_cost).sum ≤
      (ts.map (fun g =>
        ((l.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
    apply exchange
    intro j0 hj0
    exact H_all_jobs_from_taskset j0
      (in_arrivals_implies_arrived job_arrival arr_seq
        H_arrival_times_are_consistent j0 t (t + delta) hj0)
  apply le_trans h_exch
  apply List.sum_le_sum
  intro tsk' htsk'
  exact per_task_bound tsk' htsk'

end WorkloadIsBoundedByRBF

end ProofWorkloadBound

end Lemmas

end MaxArrivalsWorkloadBound

end Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
