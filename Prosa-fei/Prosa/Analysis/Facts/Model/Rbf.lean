-- Translated from: ../rt-proofs/analysis/facts/model/rbf.v
import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Definitions.Job_properties
import Prosa.Analysis.Definitions.Request_bound_function

namespace Prosa.Analysis.Facts.Model.Rbf

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Util.Rel
open Prosa.Util.Sum
open Prosa.Analysis.Facts.Behavior.Arrivals

-- Sub-helpers for list sum partitioning
private theorem list_sum_map_add {β : Type*} (ks : List β) (p q : β → ℕ) :
    (ks.map (fun k => p k + q k)).sum = (ks.map p).sum + (ks.map q).sum := by
  induction ks with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons]; omega

private theorem list_mem_le_ite_sum {β : Type*} [DecidableEq β]
    : ∀ (ks : List β) (c : ℕ) (b : β), b ∈ ks →
    c ≤ (ks.map (fun k => if b == k then c else 0)).sum
  | [], _, _, hb => nomatch hb
  | k :: rest, c, b, hb => by
    simp only [List.map_cons, List.sum_cons]
    cases List.mem_cons.mp hb with
    | inl heq => rw [show (b == k) = true from beq_iff_eq.mpr heq]; simp
    | inr hmem => have := list_mem_le_ite_sum rest c b hmem; omega

-- Helper: partition a list sum by a grouping function
-- If every element maps to some group in `groups`, then
-- the total sum ≤ sum of per-group sums
theorem list_sum_le_partition_sum {α β : Type*} [DecidableEq β]
    : ∀ (l : List α) (groups : List β) (f : α → ℕ) (g : α → β),
    (∀ x ∈ l, g x ∈ groups) →
    (l.map f).sum ≤
    (groups.map (fun k => ((l.filter (fun x => g x == k)).map f).sum)).sum
  | [], _, _, _, _ => by simp
  | a :: rest, groups, f, g, h_cover => by
    simp only [List.map_cons, List.sum_cons]
    have ha : g a ∈ groups := h_cover a (.head rest)
    have hrest : ∀ b ∈ rest, g b ∈ groups := fun b hb => h_cover b (.tail a hb)
    have ih := list_sum_le_partition_sum rest groups f g hrest
    -- Decompose filter for (a :: rest): each group k gets a iff g a == k
    have hfilt : ∀ k, ((a :: rest).filter (fun x => g x == k)).map f =
        (if g a == k then [f a] else []) ++ ((rest.filter (fun x => g x == k)).map f) := by
      intro k; simp only [List.filter_cons]; split <;> simp
    simp_rw [hfilt, List.sum_append]
    have hcond : ∀ k, ((if g a == k then [f a] else []) : List ℕ).sum =
        if g a == k then f a else 0 := by
      intro k; split <;> simp
    simp_rw [hcond]
    calc f a + (rest.map f).sum
      ≤ f a + (groups.map (fun k => ((rest.filter (fun x => g x == k)).map f).sum)).sum :=
          Nat.add_le_add_left ih _
      _ ≤ (groups.map (fun k => (if g a == k then f a else 0) +
              ((rest.filter (fun x => g x == k)).map f).sum)).sum := by
          rw [list_sum_map_add]
          exact Nat.add_le_add_right (list_mem_le_ite_sum groups (f a) (g a) ha) _

section ProofWorkloadBound

  variable {Task : TaskType}
  variable [TaskCost Task]
  variable [DecidableEq Task]

  variable {Job : JobType}
  variable [JobTask Job Task]
  variable [JobArrival Job]
  variable [JobCost Job]
  variable [DecidableEq Job]

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
  variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

  variable (sched : schedule (processor_state Job))
  variable (H_jobs_come_from_arrival_sequence :
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq)

  variable [FP_policy Task]

  variable (ts : List Task)

  variable (tsk : Task)
  variable (H_tsk_in_ts : tsk ∈ ts)

  variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

  variable (H_all_jobs_from_taskset : all_jobs_from_taskset (Task := Task) arr_seq ts)

  variable [MaxArrivals Task]
  variable (H_is_arrival_bound : taskset_respects_max_arrivals arr_seq ts)

  variable (j : Job)
  variable (H_j_arrives : arrives_in arr_seq j)
  variable (H_job_of_tsk : job_task j = tsk)

  section WorkloadIsBoundedByRBF

    variable (t : instant)
    variable (delta : instant)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_tsk_in_ts H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
    theorem task_workload_le_num_of_arrivals_times_cost :
        workload_of_jobs (job_of_task tsk) (arrivals_between arr_seq t (t + delta))
        ≤ task_cost tsk * number_of_task_arrivals arr_seq tsk t (t + delta) := by
      simp only [workload_of_jobs, number_of_task_arrivals, task_arrivals_between, job_of_task]
      exact sum_majorant_constant _ _ _ (task_cost tsk) (fun a ha hP => by
        have harr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent a _ _ ha
        have hvc : valid_job_cost (Task := Task) a := H_valid_job_cost a harr
        simp only [valid_job_cost] at hvc
        have htsk : job_task (Task := Task) a = tsk := (beq_iff_eq (a := job_task a) (b := tsk)).mp hP
        rw [htsk] at hvc; exact hvc)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_tsk_in_ts H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
    theorem task_workload_le_task_rbf :
        workload_of_jobs (job_of_task tsk) (arrivals_between arr_seq t (t + delta))
        ≤ task_request_bound_function tsk delta := by
      simp only [task_request_bound_function]
      apply le_trans (b := task_cost tsk * number_of_task_arrivals arr_seq tsk t (t + delta))
      · -- workload ≤ cost * #arrivals
        simp only [workload_of_jobs, number_of_task_arrivals, task_arrivals_between, job_of_task]
        exact sum_majorant_constant _ _ _ (task_cost tsk) (fun a ha hP => by
          have harr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent a _ _ ha
          have hvc : valid_job_cost (Task := Task) a := H_valid_job_cost a harr
          simp only [valid_job_cost] at hvc
          have htsk : job_task (Task := Task) a = tsk := (beq_iff_eq (a := job_task a) (b := tsk)).mp hP
          rw [htsk] at hvc; exact hvc)
      · -- cost * #arrivals ≤ cost * max_arrivals
        apply Nat.mul_le_mul_left
        have h1 := H_is_arrival_bound tsk H_tsk_in_ts t (t + delta) (Nat.le_add_right t delta)
        simp only [Nat.add_sub_cancel_left] at h1
        exact h1

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_tsk_in_ts H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
    theorem total_workload_le_total_rbf :
        workload_of_jobs
          (fun (j_other : Job) => (FP_to_JLFP Job Task).hep_job j_other j &&
            (!same_task (Task := Task) j_other j))
          (arrivals_between arr_seq t (t + delta))
        ≤ total_ohep_request_bound_function_FP ts tsk delta := by
      -- Relate job predicate P to task predicate Q
      -- P j0 = hep_task (job_task j0) tsk && !(job_task j0 == tsk)
      -- Q tsk' = hep_task tsk' tsk && decide (tsk' ≠ tsk)
      have hP : ∀ j0 : Job,
          ((FP_to_JLFP Job Task).hep_job j0 j && (!same_task (Task := Task) j0 j)) =
          (hep_task (job_task (Task := Task) j0) tsk && decide (job_task (Task := Task) j0 ≠ tsk)) := by
        intro j0; unfold FP_to_JLFP same_task; rw [H_job_of_tsk]
        cases h : (job_task (Task := Task) j0 == tsk) <;> simp_all [beq_iff_eq, beq_eq_false_iff_ne]
      set l := arrivals_between arr_seq t (t + delta) with hl
      -- Apply partition lemma
      have h_cover : ∀ j0 ∈ l.filter (fun j0 => (FP_to_JLFP Job Task).hep_job j0 j && (!same_task (Task := Task) j0 j)),
          (job_task (Task := Task) j0) ∈
            ts.filter (fun tsk' => hep_task tsk' tsk && decide (tsk' ≠ tsk)) := by
        intro j0 hj0; rw [List.mem_filter] at hj0 ⊢
        constructor
        · exact H_all_jobs_from_taskset j0
            (in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent j0 _ _ hj0.1)
        · rw [← hP]; exact hj0.2
      have h_part := list_sum_le_partition_sum _ _ job_cost (fun j => job_task (Task := Task) j) h_cover
      simp only [workload_of_jobs]
      apply le_trans h_part
      simp only [total_ohep_request_bound_function_FP, task_request_bound_function]
      -- Pointwise bound over ts.filter Q
      set Q := fun tsk' => hep_task tsk' tsk && decide (tsk' ≠ tsk)
      conv_lhs => rw [show ts.filter Q = (ts.filter Q).filter (fun (_ : Task) => true) from (List.filter_true _).symm]
      conv_rhs => rw [show ts.filter Q = (ts.filter Q).filter (fun (_ : Task) => true) from (List.filter_true _).symm]
      apply leq_sum_seq
      intro tsk' htsk' _
      -- Simplify double filter: for tsk' with Q tsk', P j = true whenever job_task j = tsk'
      -- So (l.filter P).filter (job_task · == tsk') = l.filter (job_task · == tsk')
      have htsk'_Q : Q tsk' = true := (List.mem_filter.mp htsk').2
      have h_filter_eq : (l.filter (fun j0 => (FP_to_JLFP Job Task).hep_job j0 j && (!same_task (Task := Task) j0 j))).filter
            (fun j0 => job_task (Task := Task) j0 == tsk') =
          l.filter (fun j0 => job_task (Task := Task) j0 == tsk') := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro j0 _hj0
        by_cases hq : (job_task (Task := Task) j0 = tsk')
        · simp only [beq_iff_eq.mpr hq, Bool.and_true]
          rw [hP, hq]
          exact htsk'_Q
        · have hbeq : (job_task (Task := Task) j0 == tsk') = false := beq_eq_false_iff_ne.mpr hq
          simp [hbeq]
      rw [h_filter_eq]
      apply le_trans (b := task_cost tsk' * (l.filter (fun j0 => job_task (Task := Task) j0 == tsk')).length)
      · exact sum_majorant_constant _ _ _ (task_cost tsk') (fun a ha hPa => by
          have harr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent a _ _ ha
          have hvc : valid_job_cost (Task := Task) a := H_valid_job_cost a harr
          simp only [valid_job_cost] at hvc
          rw [(beq_iff_eq (a := job_task a) (b := tsk')).mp hPa] at hvc; exact hvc)
      · apply Nat.mul_le_mul_left
        have h1 := H_is_arrival_bound tsk' (List.mem_filter.mp htsk').1 t (t + delta) (Nat.le_add_right t delta)
        simp only [Nat.add_sub_cancel_left] at h1
        exact h1

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_tsk_in_ts H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
    theorem total_workload_le_total_rbf' :
        workload_of_jobs
          (fun (j_other : Job) => (FP_to_JLFP Job Task).hep_job j_other j)
          (arrivals_between arr_seq t (t + delta))
        ≤ total_hep_request_bound_function_FP ts tsk delta := by
      -- Relate job predicate to task predicate
      have hP : ∀ j0 : Job,
          (FP_to_JLFP Job Task).hep_job j0 j = hep_task (job_task (Task := Task) j0) tsk := by
        intro j0; show hep_task (job_task (Task := Task) j0) (job_task j) =
          hep_task (job_task (Task := Task) j0) tsk; rw [H_job_of_tsk]
      set l := arrivals_between arr_seq t (t + delta) with hl
      -- Apply partition lemma
      have h_cover : ∀ j0 ∈ l.filter (fun j0 => (FP_to_JLFP Job Task).hep_job j0 j),
          (job_task (Task := Task) j0) ∈ ts.filter (fun tsk' => hep_task tsk' tsk) := by
        intro j0 hj0; rw [List.mem_filter] at hj0 ⊢
        constructor
        · exact H_all_jobs_from_taskset j0
            (in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent j0 _ _ hj0.1)
        · rw [← hP]; exact hj0.2
      have h_part := list_sum_le_partition_sum _ _ job_cost (fun j => job_task (Task := Task) j) h_cover
      simp only [workload_of_jobs]
      apply le_trans h_part
      simp only [total_hep_request_bound_function_FP, task_request_bound_function]
      -- Pointwise bound
      set Q := fun tsk' => hep_task tsk' tsk
      conv_lhs => rw [show ts.filter Q = (ts.filter Q).filter (fun (_ : Task) => true) from (List.filter_true _).symm]
      conv_rhs => rw [show ts.filter Q = (ts.filter Q).filter (fun (_ : Task) => true) from (List.filter_true _).symm]
      apply leq_sum_seq
      intro tsk' htsk' _
      -- Simplify double filter: for tsk' with hep_task tsk' tsk, the job pred is also true
      have htsk'_Q : hep_task tsk' tsk = true := (List.mem_filter.mp htsk').2
      have h_filter_eq : (l.filter (fun j0 => (FP_to_JLFP Job Task).hep_job j0 j)).filter
            (fun j0 => job_task (Task := Task) j0 == tsk') =
          l.filter (fun j0 => job_task (Task := Task) j0 == tsk') := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro j0 _hj0
        cases hq : (job_task (Task := Task) j0 == tsk') <;> simp_all
      rw [h_filter_eq]
      apply le_trans (b := task_cost tsk' * (l.filter (fun j0 => job_task (Task := Task) j0 == tsk')).length)
      · exact sum_majorant_constant _ _ _ (task_cost tsk') (fun a ha hPa => by
          have harr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent a _ _ ha
          have hvc : valid_job_cost (Task := Task) a := H_valid_job_cost a harr
          simp only [valid_job_cost] at hvc
          rw [(beq_iff_eq (a := job_task a) (b := tsk')).mp hPa] at hvc; exact hvc)
      · apply Nat.mul_le_mul_left
        have h1 := H_is_arrival_bound tsk' (List.mem_filter.mp htsk').1 t (t + delta) (Nat.le_add_right t delta)
        simp only [Nat.add_sub_cancel_left] at h1
        exact h1

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_tsk_in_ts H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_bound H_j_arrives H_job_of_tsk in
    theorem total_workload_le_total_rbf'' :
        workload_of_jobs (fun (_ : Job) => true) (arrivals_between arr_seq t (t + delta))
        ≤ total_request_bound_function ts delta := by
      -- Phase 1: partition workload by task
      have h_in_ts : ∀ j0 ∈ arrivals_between arr_seq t (t + delta), (job_task j0 : Task) ∈ ts :=
        fun j0 hj0 => H_all_jobs_from_taskset j0
          (in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent j0 _ _ hj0)
      have h_partition : workload_of_jobs (fun (_ : Job) => true) (arrivals_between arr_seq t (t + delta)) ≤
          (ts.map (fun tsk' => workload_of_jobs (job_of_task tsk') (arrivals_between arr_seq t (t + delta)))).sum := by
        simp only [workload_of_jobs, job_of_task]
        rw [List.filter_true]
        exact list_sum_le_partition_sum _ ts job_cost (fun j => job_task j) h_in_ts
      -- Phase 2: bound each per-task workload by task_rbf
      apply le_trans h_partition
      simp only [total_request_bound_function, task_request_bound_function]
      -- Goal: (ts.map F).sum ≤ (ts.map G).sum
      -- Use leq_sum_seq with P = fun _ => true
      conv_lhs => rw [show ts = ts.filter (fun (_ : Task) => true) from (List.filter_true ts).symm]
      conv_rhs => rw [show ts = ts.filter (fun (_ : Task) => true) from (List.filter_true ts).symm]
      apply leq_sum_seq
      intro tsk' _htsk' _
      simp only [workload_of_jobs, number_of_task_arrivals, task_arrivals_between, job_of_task]
      apply le_trans (b := task_cost tsk' * (((arrivals_between arr_seq t (t + delta)).filter
          (fun j => job_task j == tsk')).length))
      · exact sum_majorant_constant _ _ _ (task_cost tsk') (fun a ha hP => by
          have harr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent a _ _ ha
          have hvc : valid_job_cost (Task := Task) a := H_valid_job_cost a harr
          simp only [valid_job_cost] at hvc
          have htsk_eq : job_task (Task := Task) a = tsk' := (beq_iff_eq (a := job_task a) (b := tsk')).mp hP
          rw [htsk_eq] at hvc; exact hvc)
      · apply Nat.mul_le_mul_left
        have hmem : tsk' ∈ ts := _htsk'
        have h1 := H_is_arrival_bound tsk' hmem t (t + delta) (Nat.le_add_right t delta)
        simp only [Nat.add_sub_cancel_left] at h1
        exact h1

  end WorkloadIsBoundedByRBF

end ProofWorkloadBound

section RequestBoundFunctions

  variable {Task : TaskType}
  variable [TaskCost Task]
  variable [DecidableEq Task]

  variable {Job : JobType}
  variable [JobTask Job Task]
  variable [JobArrival Job]
  variable [DecidableEq Job]

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

  variable (tsk : Task)

  variable [MaxArrivals Task]
  variable (H_valid_arrival_curve : valid_arrival_curve tsk (max_arrivals tsk))
  variable (H_is_arrival_curve : respects_max_arrivals arr_seq tsk (max_arrivals tsk))

  include H_arrival_times_are_consistent H_valid_arrival_curve H_is_arrival_curve in
  theorem task_rbf_0_zero :
      task_request_bound_function tsk 0 = 0 := by
    simp [task_request_bound_function, H_valid_arrival_curve.1]

  include H_arrival_times_are_consistent H_valid_arrival_curve H_is_arrival_curve in
  theorem task_rbf_monotone :
      Prosa.Util.Rel.monotone (task_request_bound_function tsk) Nat.ble := by
    intro x y hle
    unfold task_request_bound_function
    have hm := H_valid_arrival_curve.2 x y hle
    simp only [Nat.ble_eq, decide_eq_true_eq] at hm ⊢
    exact Nat.mul_le_mul_left _ hm

  variable [JobCost Job]

  variable (j : Job)
  variable (H_j_arrives : arrives_in arr_seq j)
  variable (H_job_of_tsk : job_task j = tsk)

  include H_valid_arrival_curve in
  theorem task_rbf_1_ge_task_cost
      (_use_arr := arr_seq)
      (_use_consist := H_arrival_times_are_consistent)
      (_use_curve := H_is_arrival_curve)
      (_use_j := j)
      (_use_arrives := H_j_arrives)
      (_use_of_tsk := H_job_of_tsk) :
      task_request_bound_function tsk 1 ≥ task_cost tsk := by
    simp only [task_request_bound_function, ge_iff_le]
    suffices h : 1 ≤ max_arrivals tsk 1 by
      calc task_cost tsk = task_cost tsk * 1 := (Nat.mul_one _).symm
        _ ≤ task_cost tsk * max_arrivals tsk 1 := Nat.mul_le_mul_left _ h
    -- Show max_arrivals tsk 1 ≥ 1 using j's existence
    -- j is in task_arrivals_between, so number_of_task_arrivals ≥ 1
    have hlen : 1 ≤ number_of_task_arrivals arr_seq tsk (job_arrival j) (job_arrival j + 1) := by
      simp only [number_of_task_arrivals, task_arrivals_between]
      apply List.length_pos_of_mem (a := j)
      apply List.mem_filter.mpr
      constructor
      · obtain ⟨t_arr, harr_at⟩ := H_j_arrives
        have hcons : job_arrival j = t_arr := H_arrival_times_are_consistent j t_arr harr_at
        rw [← hcons] at harr_at
        -- harr_at : j ∈ arrivals_at arr_seq (job_arrival j)
        show j ∈ arrivals_between arr_seq (job_arrival j) (job_arrival j + 1)
        simp only [arrivals_between, Prosa.Util.Notation.bigCat, List.mem_flatten, List.mem_map,
          List.mem_range]
        exact ⟨arrivals_at arr_seq (job_arrival j),
          ⟨0, by omega, by simp⟩, harr_at⟩
      · simp [H_job_of_tsk]
    calc 1 ≤ number_of_task_arrivals arr_seq tsk (job_arrival j) (job_arrival j + 1) := hlen
      _ ≤ max_arrivals tsk (job_arrival j + 1 - job_arrival j) :=
        _use_curve (job_arrival j) (job_arrival j + 1) (Nat.le_add_right _ _)
      _ = max_arrivals tsk 1 := by
        congr 1
        exact Nat.add_sub_cancel_left (job_arrival j) 1

end RequestBoundFunctions

end Prosa.Analysis.Facts.Model.Rbf
