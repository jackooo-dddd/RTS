-- Translated from: ../rt-proofs/classic/analysis/apa/interference_bound_edf.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Platform
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Interference_edf
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Analysis.Apa.Workload_bound
import Prosa.Classic.Analysis.Apa.Interference_bound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Apa.Interference_bound_edf

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Apa.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Interference_edf
open Prosa.Classic.Model.Schedule.Apa.Interference_edf.InterferenceEDF
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Apa.Interference_bound.InterferenceBoundGeneric
open Prosa.Util.Div_mod

namespace InterferenceBoundEDF

section SpecificBoundDef

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable (tsk : sporadic_task)
variable (tsk_other : sporadic_task)
variable (R_other : Time)

def edf_specific_interference_bound : ℕ :=
  let d_tsk := task_deadline tsk
  let e_other := task_cost tsk_other
  let p_other := task_period tsk_other
  let d_other := task_deadline tsk_other
  (div_floor d_tsk p_other) * e_other +
  min e_other (d_tsk % p_other - (d_other - R_other))

end SpecificBoundDef

section TotalInterferenceBoundEDF

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)

variable (tsk : sporadic_task)
variable (alpha' : affinity num_cpus)
variable (R_prev : List (task_with_response_time sporadic_task))
variable (delta : Time)

section RecallInterferenceBounds

variable (tsk_R : task_with_response_time sporadic_task)

def interference_bound_edf : ℕ :=
  let basic_interference_bound := interference_bound_generic task_cost task_period tsk delta tsk_R
  let edf_specific_bound := edf_specific_interference_bound task_cost task_period task_deadline
    tsk tsk_R.1 tsk_R.2
  min basic_interference_bound edf_specific_bound

end RecallInterferenceBounds

section TotalInterference

private instance decDifferent_task_in_local (tsk_other : sporadic_task) :
    Decidable (different_task_in alpha tsk alpha' tsk_other) :=
  if h1 : tsk_other ≠ tsk then
    if h2 : affinity_intersects alpha' (alpha tsk_other) then
      isTrue ⟨h1, h2⟩
    else
      isFalse (fun ⟨_, h⟩ => h2 h)
  else
    isFalse (fun ⟨h, _⟩ => h1 h)

def total_interference_bound_edf : ℕ :=
  (R_prev.filter (fun tsk_R =>
    decide (different_task_in alpha tsk alpha' tsk_R.1))).map
    (fun tsk_R => interference_bound_edf task_cost task_period task_deadline tsk delta tsk_R)
    |>.sum

end TotalInterference

end TotalInterferenceBoundEDF

section ProofSpecificBound

attribute [local instance] Classical.propDecidable

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (arr_seq : arrival_sequence Job)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)
variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_at_least_one_cpu : num_cpus > 0)

variable (alpha : task_affinity sporadic_task num_cpus)

variable (ts : List sporadic_task)
variable (all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)
variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_edf_weak_APA_scheduler :
  Prosa.Classic.Model.Schedule.Apa.Interference_edf.respects_JLFP_policy_under_weak_APA
    job_arrival job_cost job_task arr_seq sched alpha
    (Prosa.Classic.Model.Schedule.Apa.Interference_edf.EDF job_arrival job_deadline))

variable (tsk_i : sporadic_task)
variable (H_tsk_i_in_task_set : tsk_i ∈ ts)

variable (j_i : Job)
variable (H_j_i_arrives : arrives_in arr_seq j_i)
variable (H_job_of_tsk_i : job_task j_i = tsk_i)

variable (tsk_k : sporadic_task)
variable (H_tsk_k_in_task_set : tsk_k ∈ ts)

variable (R_k : Time)
variable (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)

variable (delta : Time)
variable (H_delta_le_deadline : delta ≤ task_deadline tsk_i)

variable (H_all_previous_jobs_completed_on_time :
  ∀ j_k,
    arrives_in arr_seq j_k →
    job_task j_k = tsk_k →
    job_arrival j_k + R_k < job_arrival j_i + delta →
    completed job_cost sched j_k (job_arrival j_k + R_k))

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
  H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines
  H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set
  H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline
  H_delta_le_deadline H_all_previous_jobs_completed_on_time

section MainProof

private noncomputable abbrev the_interference_caused_by (j' : Job) : ℕ :=
  Prosa.Classic.Model.Schedule.Apa.Interference.job_interference
    job_arrival job_cost job_task sched alpha j_i j'
    (job_arrival j_i) (job_arrival j_i + delta)

private noncomputable abbrev the_interfering_jobs : List Job :=
  (jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter
    (fun j' => decide (job_task j' = tsk_k) &&
      decide (the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j' ≠ 0))

private noncomputable abbrev the_sorted_jobs : List Job :=
  (the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).mergeSort
    (fun x y => decide (job_arrival x ≤ job_arrival y))

section SimplifyJobSequence

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_use_another_definition :
    Prosa.Classic.Model.Schedule.Apa.Interference.task_interference
      job_arrival job_cost job_task sched alpha j_i
      tsk_k (job_arrival j_i) (job_arrival j_i + delta) ≤
    (((jobs_scheduled_between sched (job_arrival j_i)
      (job_arrival j_i + delta)).filter (fun j' => decide (job_task j' = tsk_k))).map
      (fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j')).sum := by
  sorry

theorem interference_bound_edf_simpl_by_filtering_interfering_jobs :
    (((jobs_scheduled_between sched (job_arrival j_i)
      (job_arrival j_i + delta)).filter (fun j' => decide (job_task j' = tsk_k))).map
      (fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j')).sum =
    ((the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).map
      (fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j')).sum := by
  set jsb := jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)
  set f := fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j'
  -- Filtering by task and then mapping = filtering by task+nonzero and mapping
  -- because zero-interference jobs contribute 0
  suffices h : List.sum ((jsb.filter (fun j' => decide (job_task j' = tsk_k))).map f) =
    List.sum ((jsb.filter (fun j' => decide (job_task j' = tsk_k) && decide (f j' ≠ 0))).map f) by
    exact h
  induction jsb with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases h_task : decide (job_task hd = tsk_k) = true
    · simp only [h_task, Bool.true_and]
      by_cases h_interf : decide (f hd ≠ 0) = true
      · simp only [h_interf, List.map_cons, List.sum_cons]
        rw [ih]
      · simp only [h_interf]
        simp only [decide_eq_true_eq, not_not] at h_interf
        simp only [List.map_cons, List.sum_cons]
        rw [h_interf, Nat.zero_add]
        exact ih
    · simp only [h_task, Bool.false_and]
      exact ih

theorem interference_bound_edf_simpl_by_sorting_interfering_jobs :
    ((the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).map
      (fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j')).sum =
    ((the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).map
      (fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j')).sum := by
  unfold the_sorted_jobs
  apply List.Perm.sum_eq
  apply List.Perm.map
  exact (List.mergeSort_perm _ _).symm

theorem interference_bound_edf_job_in_same_sequence :
    ∀ j,
      (j ∈ the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta) =
      (j ∈ the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta) := by
  intro j
  unfold the_sorted_jobs
  exact propext ((List.mergeSort_perm _ _).symm.mem_iff)

theorem interference_bound_edf_all_jobs_from_tsk_k :
    ∀ j,
      j ∈ the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta →
      arrives_in arr_seq j ∧
      job_task j = tsk_k ∧
      the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j ≠ 0 ∧
      j ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
  intro j h_in
  have h_in' : j ∈ the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta := by
    unfold the_sorted_jobs at h_in
    exact (List.mergeSort_perm _ _).mem_iff.mp h_in
  unfold the_interfering_jobs at h_in'
  rw [List.mem_filter] at h_in'
  obtain ⟨h_in_sched, h_pred⟩ := h_in'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_pred
  obtain ⟨h_task, h_interf⟩ := h_pred
  unfold jobs_scheduled_between at h_in_sched
  rw [List.mem_dedup] at h_in_sched
  obtain ⟨i, h_mem_i, h_range_lo, h_range_hi⟩ :=
    Prosa.Util.Bigcat.mem_bigcat_nat_exists j (job_arrival j_i) (job_arrival j_i + delta) _ h_in_sched
  rw [mem_scheduled_jobs_eq_scheduled] at h_mem_i
  have h_arrives : arrives_in arr_seq j :=
    H_jobs_come_from_arrival_sequence j i h_mem_i
  have h_in_jsb : j ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
    unfold jobs_scheduled_between
    rw [List.mem_dedup]
    exact Prosa.Util.Bigcat.mem_bigcat_nat j (job_arrival j_i) (job_arrival j_i + delta) i _
      ⟨h_range_lo, h_range_hi⟩
      ((mem_scheduled_jobs_eq_scheduled sched j i).mpr h_mem_i)
  exact ⟨h_arrives, h_task, h_interf, h_in_jsb⟩

theorem interference_bound_edf_jobs_ordered_by_arrival :
    ∀ i elem,
      i < (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).length - 1 →
      job_arrival ((the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
        i elem) ≤
      job_arrival ((the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
        (i + 1) elem) := by
  intro i elem h_lt
  set sorted := the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta
  have h_trans : ∀ (a b c : Job), decide (job_arrival a ≤ job_arrival b) = true → decide (job_arrival b ≤ job_arrival c) = true → decide (job_arrival a ≤ job_arrival c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have h_total : ∀ (a b : Job), (decide (job_arrival a ≤ job_arrival b) || decide (job_arrival b ≤ job_arrival a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total (job_arrival a) (job_arrival b)
  have h_sorted := List.pairwise_mergeSort h_trans h_total
    (the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta)
  have h_chain : List.IsChain (fun a b => decide (job_arrival a ≤ job_arrival b) = true) sorted :=
    h_sorted.isChain
  have h_ord := Prosa.Classic.Util.Sorting.sort_ordered (fun x y => decide (job_arrival x ≤ job_arrival y))
    sorted elem i h_chain h_lt
  simp only [decide_eq_true_eq] at h_ord
  exact h_ord

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_interference_le_task_cost :
    ∀ j,
      j ∈ the_interfering_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta →
      the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j ≤
      task_cost tsk_k := by
  sorry

end SimplifyJobSequence

section InterferenceFewJobs

variable (H_few_jobs :
  (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).length ≤
  div_floor (task_deadline tsk_i) (task_period tsk_k))
include H_few_jobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_few_jobs in
theorem interference_bound_edf_holds_for_at_most_n_k_jobs :
    ((the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).map
      (fun j' => the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j')).sum ≤
    edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  sorry

end InterferenceFewJobs

section InterferenceManyJobs

variable (H_many_jobs :
  div_floor (task_deadline tsk_i) (task_period tsk_k) <
  (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).length)
include H_many_jobs

theorem interference_bound_edf_at_least_one_job :
    (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).length > 0 := by
  omega

variable (elem : Job)

section FactsAboutFirstJob

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_j_fst_is_job_of_tsk_k :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    arrives_in arr_seq j_fst ∧
    job_task j_fst = tsk_k ∧
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≠ 0 ∧
    j_fst ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_j_fst_deadline :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    job_deadline j_fst = task_deadline tsk_k := by
  sorry

theorem interference_bound_edf_j_i_deadline :
    job_deadline j_i = task_deadline tsk_i := by
  have h_valid := H_valid_job_parameters j_i H_j_i_arrives
  unfold valid_sporadic_job at h_valid
  obtain ⟨_, _, h_dl⟩ := h_valid
  unfold job_deadline_eq_task_deadline at h_dl
  rw [h_dl, H_job_of_tsk_i]

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let a_fst := job_arrival j_fst
    completed job_cost sched j_fst (a_fst + R_k) →
    job_arrival j_i ≤ a_fst + R_k := by
  sorry

end FactsAboutFirstJob

section InterferenceSingleJob

variable (H_only_one_job :
  (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).length = 1)
include H_only_one_job

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job in
theorem interference_bound_edf_simpl_when_theres_one_job :
    task_deadline tsk_i % task_period tsk_k -
      (task_deadline tsk_k - R_k) =
    task_deadline tsk_i - (task_deadline tsk_k - R_k) := by
  sorry

section ResponseTimeOfSingleJobBounded

variable (H_j_fst_completed_by_rt_bound :
  let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
    0 elem
  let a_fst := job_arrival j_fst
  completed job_cost sched j_fst (a_fst + R_k))
include H_j_fst_completed_by_rt_bound

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_completed_by_rt_bound in
theorem interference_bound_edf_holds_for_single_job_that_completes_on_time :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    Prosa.Classic.Model.Schedule.Apa.Interference.job_interference
      job_arrival job_cost job_task sched alpha j_i j_fst
      (job_arrival j_i) (job_arrival j_i + delta) ≤
    task_deadline tsk_i - (task_deadline tsk_k - R_k) := by
  sorry

end ResponseTimeOfSingleJobBounded

section ResponseTimeOfSingleJobNotBounded

variable (H_j_fst_not_complete_by_rt_bound :
  let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
    0 elem
  let a_fst := job_arrival j_fst
  ¬ completed job_cost sched j_fst (a_fst + R_k))
include H_j_fst_not_complete_by_rt_bound

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_not_complete_by_rt_bound in
theorem interference_bound_edf_response_time_bound_of_j_fst_after_interval :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    job_arrival j_fst + R_k ≥ job_arrival j_i + delta := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_not_complete_by_rt_bound in
theorem interference_bound_edf_holds_for_single_job_with_big_slack :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    task_deadline tsk_i < task_deadline tsk_k - R_k →
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst = 0 := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_not_complete_by_rt_bound in
theorem interference_bound_edf_holds_for_single_job_with_small_slack :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    task_deadline tsk_i ≥ task_deadline tsk_k - R_k →
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≤
    task_deadline tsk_i - (task_deadline tsk_k - R_k) := by
  sorry

end ResponseTimeOfSingleJobNotBounded

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job in
theorem interference_bound_edf_interference_of_j_fst_limited_by_slack :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≤
    task_deadline tsk_i - (task_deadline tsk_k - R_k) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job in
theorem interference_bound_edf_holds_for_a_single_job :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≤
    edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  sorry

end InterferenceSingleJob

section InterferenceTwoOrMoreJobs

variable (num_mid_jobs : ℕ)
variable (H_at_least_two_jobs :
  (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).length =
  num_mid_jobs + 2)
include H_at_least_two_jobs

section FactsAboutFirstAndLastJobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_lst_is_job_of_tsk_k :
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    arrives_in arr_seq j_lst ∧
    job_task j_lst = tsk_k ∧
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_lst ≠ 0 ∧
    j_lst ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_lst_deadline :
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    job_deadline j_lst = task_deadline tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_fst_before_j_lst :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    job_arrival j_fst ≤ job_arrival j_lst := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_last_job_arrives_before_end_of_interval :
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    job_arrival j_lst < job_arrival j_i + delta := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_fst_completed_on_time :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let a_fst := job_arrival j_fst
    completed job_cost sched j_fst (a_fst + R_k) := by
  sorry

end FactsAboutFirstAndLastJobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_many_periods_in_between :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    let a_fst := job_arrival j_fst
    let a_lst := job_arrival j_lst
    a_lst - a_fst ≥ (num_mid_jobs + 1) * task_period tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_n_k_covers_middle_jobs_plus_one :
    div_floor (task_deadline tsk_i) (task_period tsk_k) ≥ num_mid_jobs + 1 := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_holds_for_middle_and_last_jobs :
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_lst +
    ∑ i ∈ Finset.Ico 0 num_mid_jobs,
      the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta
        ((the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
          (i + 1) elem) ≤
    div_floor (task_deadline tsk_i) (task_period tsk_k) * task_cost tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_n_k_equals_num_mid_jobs_plus_one :
    div_floor (task_deadline tsk_i) (task_period tsk_k) = num_mid_jobs + 1 := by
  sorry

section InterferenceOfFirstJob

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_remainder_ge_slack :
    task_deadline tsk_k - R_k ≤ task_deadline tsk_i % task_period tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_simpl_by_moving_to_left_side :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst +
      (task_deadline tsk_k - R_k) +
      task_deadline tsk_i / task_period tsk_k * task_period tsk_k ≤
      task_deadline tsk_i →
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≤
    task_deadline tsk_i % task_period tsk_k - (task_deadline tsk_k - R_k) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_interference_of_j_fst_bounded_by_response_time :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let a_fst := job_arrival j_fst
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≤
    ∑ _t ∈ Finset.Ico (job_arrival j_i) (a_fst + R_k), (1 : ℕ) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_bounding_interference_with_interval_lengths :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    let a_fst := job_arrival j_fst
    let a_lst := job_arrival j_lst
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst +
      (task_deadline tsk_k - R_k) +
      task_deadline tsk_i / task_period tsk_k * task_period tsk_k ≤
    ∑ _t ∈ Finset.Ico (job_arrival j_i) (a_fst + R_k), (1 : ℕ) +
    ∑ _t ∈ Finset.Ico (a_fst + R_k) (a_fst + task_deadline tsk_k), (1 : ℕ) +
    ∑ _t ∈ Finset.Ico (a_fst + task_deadline tsk_k) (a_lst + task_deadline tsk_k), (1 : ℕ) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_simpl_by_concatenation_of_intervals :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    let j_lst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      (num_mid_jobs + 1) elem
    let a_fst := job_arrival j_fst
    let a_lst := job_arrival j_lst
    ∑ _t ∈ Finset.Ico (job_arrival j_i) (a_fst + R_k), (1 : ℕ) +
    ∑ _t ∈ Finset.Ico (a_fst + R_k) (a_fst + task_deadline tsk_k), (1 : ℕ) +
    ∑ _t ∈ Finset.Ico (a_fst + task_deadline tsk_k) (a_lst + task_deadline tsk_k), (1 : ℕ) =
    (a_lst + task_deadline tsk_k) - job_arrival j_i := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack :
    let j_fst := (the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
      0 elem
    the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta j_fst ≤
    task_deadline tsk_i % task_period tsk_k - (task_deadline tsk_k - R_k) := by
  sorry

end InterferenceOfFirstJob

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_holds_for_multiple_jobs :
    ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2),
      the_interference_caused_by job_arrival job_cost job_task sched alpha j_i delta
        ((the_sorted_jobs job_arrival job_cost job_task sched alpha j_i tsk_k delta).getD
          i elem) ≤
    edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  sorry

end InterferenceTwoOrMoreJobs

end InterferenceManyJobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_weak_APA_scheduler H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_bounds_interference :
    Prosa.Classic.Model.Schedule.Apa.Interference.task_interference
      job_arrival job_cost job_task sched alpha j_i
      tsk_k (job_arrival j_i) (job_arrival j_i + delta) ≤
    edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  sorry

end MainProof

end ProofSpecificBound

section MonotonicitySpecificBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable (tsk tsk_other : sporadic_task)
variable (H_period_positive : task_period tsk_other > 0)

variable (delta delta' R R' : Time)
variable (H_delta_monotonic : delta ≤ delta')
variable (H_response_time_monotonic : R ≤ R')
variable (H_cost_le_rt_bound : task_cost tsk_other ≤ R)

include H_period_positive H_delta_monotonic H_response_time_monotonic H_cost_le_rt_bound

include H_period_positive H_delta_monotonic H_response_time_monotonic H_cost_le_rt_bound in
theorem interference_bound_edf_monotonic :
    interference_bound_edf task_cost task_period task_deadline tsk delta (tsk_other, R) ≤
    interference_bound_edf task_cost task_period task_deadline tsk delta' (tsk_other, R') := by
  sorry

end MonotonicitySpecificBound

end InterferenceBoundEDF

end Prosa.Classic.Analysis.Apa.Interference_bound_edf
