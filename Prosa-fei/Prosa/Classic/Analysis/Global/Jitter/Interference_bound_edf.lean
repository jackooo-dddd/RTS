-- Translated from: ../rt-proofs/classic/analysis/global/jitter/interference_bound_edf.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Analysis.Global.Jitter.Workload_bound
import Prosa.Classic.Analysis.Global.Jitter.Interference_bound
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf
import Prosa.Classic.Util.Div_mod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Jitter.Interference_bound_edf

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence (arrival_sequence arrives_in)
open Prosa.Classic.Model.Arrival.Basic.Job (valid_sporadic_job)
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Interference
open Prosa.Classic.Model.Schedule.Global.Response_time
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound.WorkloadBoundJitter
open Prosa.Classic.Analysis.Global.Jitter.Interference_bound
open Prosa.Classic.Analysis.Global.Jitter.Interference_bound.InterferenceBoundJitter
open Prosa.Util.Div_mod

attribute [local instance] Classical.propDecidable

namespace InterferenceBoundEDFJitter

section SpecificBoundDef

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable (tsk : sporadic_task)

variable (delta : Time)

variable (tsk_other : sporadic_task)
variable (R_other : Time)

noncomputable def edf_specific_interference_bound : ℕ :=
  let d_tsk := task_deadline tsk
  let e_other := task_cost tsk_other
  let p_other := task_period tsk_other
  let d_other := task_deadline tsk_other
  let j_other := task_jitter tsk_other
  div_floor d_tsk p_other * e_other +
    min e_other (d_tsk % p_other - (d_other - R_other - j_other))

end SpecificBoundDef

section TotalInterferenceBoundEDF

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable (tsk : sporadic_task)

variable (R_prev : List (sporadic_task × Time))

variable (delta : Time)

section RecallInterferenceBounds

variable (tsk_R : sporadic_task × Time)

noncomputable def interference_bound_edf : ℕ :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  let basic_interference_bound :=
    interference_bound_generic task_cost task_period task_jitter tsk delta tsk_R
  let edf_specific_bound :=
    edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_other R_other
  min basic_interference_bound edf_specific_bound

end RecallInterferenceBounds

section TotalInterference

noncomputable def total_interference_bound_edf : ℕ :=
  ((R_prev.filter (fun p => different_task tsk p.1)).map
    (fun tsk_R => interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta tsk_R)).sum

end TotalInterference

end TotalInterferenceBoundEDF

section ProofSpecificBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)

variable {arr_seq : arrival_sequence Job}

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)
variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
      job_deadline job_task job_jitter j)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_execute_after_jitter :
  Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.jobs_execute_after_jitter
    job_arrival job_jitter sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_at_least_one_cpu : num_cpus > 0)

variable (ts : List sporadic_task)
variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)
variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_work_conserving :
  Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.work_conserving
    job_arrival job_cost job_jitter arr_seq sched)
variable (H_edf_policy :
  InterferenceEDF.respects_JLFP_policy_edf
    job_arrival job_cost job_jitter arr_seq sched
    (EDF job_arrival job_deadline))

variable (tsk_i : sporadic_task)
variable (H_tsk_i_in_task_set : tsk_i ∈ ts)

variable (j_i : Job)
variable (H_j_i_arrives : arrives_in arr_seq j_i)
variable (H_job_of_tsk_i : job_task j_i = tsk_i)

variable (tsk_k : sporadic_task)
variable (H_tsk_k_in_task_set : tsk_k ∈ ts)

variable (R_k : Time)
variable (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)

variable (delta : Time)
variable (H_delta_le_deadline : delta ≤ task_deadline tsk_i)

variable (H_all_previous_jobs_completed_on_time :
  ∀ j_k,
    arrives_in arr_seq j_k →
    job_task j_k = tsk_k →
    job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
    completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k))

section MainProof

noncomputable def interference_caused_by_jitter
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j_i j : Job) (t1 t2 : Time) : ℕ :=
  InterferenceEDF.job_interference_edf job_arrival job_cost job_jitter sched j_i j t1 t2

noncomputable def interfering_jobs_jitter
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j_i : Job) (tsk_k : sporadic_task) (t1 t2 : Time) : List Job :=
  (jobs_scheduled_between sched t1 t2).filter (fun j' =>
    decide (job_task j' = tsk_k) &&
    decide (interference_caused_by_jitter job_arrival job_cost job_jitter sched j_i j' t1 t2 ≠ 0))

noncomputable def sorted_jobs_jitter
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j_i : Job) (tsk_k : sporadic_task) (t1 t2 : Time) : List Job :=
  (interfering_jobs_jitter job_arrival job_cost job_task job_jitter sched j_i tsk_k t1 t2).mergeSort
    (fun x y => decide (job_arrival x ≤ job_arrival y))

noncomputable abbrev the_t1 := job_arrival j_i + job_jitter j_i
noncomputable abbrev the_t2 := the_t1 job_arrival job_jitter j_i + delta

noncomputable abbrev the_x :=
  ∑ t ∈ Finset.Ico (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta),
    ∑ cpu : Fin num_cpus,
      if (ScheduleWithJitter.backlogged job_arrival job_cost job_jitter sched j_i t ∧
          ScheduleOfSporadicTaskWithJitter.task_scheduled_on job_task sched tsk_k cpu t = true)
      then 1 else 0

noncomputable abbrev the_interference_bound :=
  edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k

noncomputable abbrev the_sorted :=
  sorted_jobs_jitter job_arrival job_cost job_task job_jitter sched j_i tsk_k
    (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta)

noncomputable abbrev the_interfering :=
  interfering_jobs_jitter job_arrival job_cost job_task job_jitter sched j_i tsk_k
    (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta)

noncomputable abbrev the_icb (j : Job) (delta' : Time) :=
  interference_caused_by_jitter job_arrival job_cost job_jitter sched j_i j
    (the_t1 job_arrival job_jitter j_i) (the_t1 job_arrival job_jitter j_i + delta')

noncomputable abbrev the_D_i := task_deadline tsk_i
noncomputable abbrev the_D_k := task_deadline tsk_k
noncomputable abbrev the_p_k := task_period tsk_k
noncomputable abbrev the_J_i := task_jitter tsk_i
noncomputable abbrev the_J_k := task_jitter tsk_k
noncomputable abbrev the_n_k := div_floor (task_deadline tsk_i) (task_period tsk_k)

section SimplifyJobSequence

include H_jobs_come_from_arrival_sequence H_valid_job_parameters
  H_completed_jobs_dont_execute H_sequential_jobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_use_another_definition :
    the_x job_arrival job_cost job_task job_jitter sched j_i tsk_k delta ≤
      ((the_interfering job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).map
        (fun j => the_icb job_arrival job_cost job_jitter sched j_i j delta)).sum := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_simpl_by_filtering_interfering_jobs :
    ∑ j ∈ ((jobs_scheduled_between sched
        (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta)).filter
        (fun j => decide (job_task j = tsk_k))).toFinset,
      the_icb job_arrival job_cost job_jitter sched j_i j delta =
    ((the_interfering job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).map
      (fun j => the_icb job_arrival job_cost job_jitter sched j_i j delta)).sum := by
  sorry

theorem interference_bound_edf_simpl_by_sorting_interfering_jobs :
    ((the_interfering job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).map
      (fun j => the_icb job_arrival job_cost job_jitter sched j_i j delta)).sum =
    ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).map
      (fun j => the_icb job_arrival job_cost job_jitter sched j_i j delta)).sum := by
  unfold the_sorted sorted_jobs_jitter
  apply List.Perm.sum_eq
  apply List.Perm.map
  exact (List.mergeSort_perm _ _).symm

theorem interference_bound_edf_job_in_same_sequence :
    ∀ j,
      (j ∈ the_interfering job_arrival job_cost job_task job_jitter sched j_i tsk_k delta) =
        (j ∈ the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta) := by
  intro j
  unfold the_sorted sorted_jobs_jitter
  exact propext ((List.mergeSort_perm _ _).symm.mem_iff)

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_all_jobs_from_tsk_k :
    ∀ j,
      j ∈ the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta →
      arrives_in arr_seq j ∧
      job_task j = tsk_k ∧
      the_icb job_arrival job_cost job_jitter sched j_i j delta ≠ 0 ∧
      j ∈ jobs_scheduled_between sched
        (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta) := by
  sorry

theorem interference_bound_edf_jobs_ordered_by_arrival :
    ∀ (i : ℕ) (elem : Job),
      i < (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).length - 1 →
      job_arrival ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD i elem) ≤
        job_arrival ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (i + 1) elem) := by
  intro i elem h_lt
  have h_total : ∀ (a b : Job), (decide (job_arrival a ≤ job_arrival b) || decide (job_arrival b ≤ job_arrival a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total (job_arrival a) (job_arrival b)
  have h_trans : ∀ (a b c : Job), decide (job_arrival a ≤ job_arrival b) = true → decide (job_arrival b ≤ job_arrival c) = true → decide (job_arrival a ≤ job_arrival c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have h_sorted := List.pairwise_mergeSort h_trans h_total
    (the_interfering job_arrival job_cost job_task job_jitter sched j_i tsk_k delta)
  have h_chain : List.IsChain (fun a b => decide (job_arrival a ≤ job_arrival b) = true)
    (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta) :=
    h_sorted.isChain
  have h_ord := Prosa.Classic.Util.Sorting.sort_ordered (fun x y => decide (job_arrival x ≤ job_arrival y))
    (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta) elem i h_chain h_lt
  simp only [decide_eq_true_eq] at h_ord
  exact h_ord

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_interference_le_task_cost :
    ∀ j,
      j ∈ the_interfering job_arrival job_cost job_task job_jitter sched j_i tsk_k delta →
      the_icb job_arrival job_cost job_jitter sched j_i j delta ≤ task_cost tsk_k := by
  sorry

end SimplifyJobSequence

section InterferenceFewJobs

variable (H_few_jobs :
  (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).length ≤
    the_n_k task_deadline task_period tsk_i tsk_k)

include H_jobs_come_from_arrival_sequence H_valid_job_parameters
  H_completed_jobs_dont_execute H_sequential_jobs H_few_jobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_few_jobs in
theorem interference_bound_edf_holds_for_at_most_n_k_jobs :
    ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).map
      (fun j => the_icb job_arrival job_cost job_jitter sched j_i j delta)).sum ≤
      the_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  sorry

end InterferenceFewJobs

section InterferenceManyJobs

variable (H_many_jobs :
  the_n_k task_deadline task_period tsk_i tsk_k <
    (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).length)

include H_jobs_come_from_arrival_sequence H_valid_job_parameters
  H_completed_jobs_dont_execute H_sequential_jobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_at_least_one_job :
    (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).length > 0 := by
  sorry

variable (elem : Job)

section FactsAboutFirstJob

include H_many_jobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_j_fst_is_job_of_tsk_k :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    arrives_in arr_seq j_fst ∧
    job_task j_fst = tsk_k ∧
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta ≠ 0 ∧
    j_fst ∈ jobs_scheduled_between sched
      (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_j_fst_deadline :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    job_deadline j_fst = task_deadline tsk_k := by
  intro j_fst
  sorry

include H_j_i_arrives H_job_of_tsk_i

theorem interference_bound_edf_j_i_deadline :
    job_deadline j_i = task_deadline tsk_i := by
  have h_valid := H_valid_job_parameters j_i H_j_i_arrives
  unfold valid_sporadic_job_with_jitter at h_valid
  obtain ⟨h_valid_job, _⟩ := h_valid
  unfold valid_sporadic_job at h_valid_job
  obtain ⟨_, _, h_dl⟩ := h_valid_job
  unfold Prosa.Classic.Model.Arrival.Basic.Job.job_deadline_eq_task_deadline at h_dl
  rw [h_dl, H_job_of_tsk_i]

include H_all_previous_jobs_completed_on_time H_R_k_le_deadline
  H_tsk_k_in_task_set H_constrained_deadlines H_valid_task_parameters

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs in
theorem interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let a_fst := job_arrival j_fst
    completed job_cost sched j_fst (a_fst + the_J_k task_jitter tsk_k + R_k) →
    the_t1 job_arrival job_jitter j_i ≤ a_fst + the_J_k task_jitter tsk_k + R_k := by
  sorry

end FactsAboutFirstJob

section InterferenceSingleJob

variable (H_only_one_job :
  (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).length = 1)

include H_many_jobs H_valid_task_parameters H_tsk_k_in_task_set
  H_constrained_deadlines H_R_k_le_deadline H_j_i_arrives H_job_of_tsk_i
  H_all_previous_jobs_completed_on_time

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job in
theorem interference_bound_edf_simpl_when_theres_one_job :
    the_D_i task_deadline tsk_i % the_p_k task_period tsk_k -
      (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) =
    the_D_i task_deadline tsk_i - (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) := by
  sorry

section ResponseTimeOfSingleJobBounded

variable (H_j_fst_completed_by_rt_bound :
  let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
  let a_fst := job_arrival j_fst
  completed job_cost sched j_fst (a_fst + the_J_k task_jitter tsk_k + R_k))

include H_j_fst_completed_by_rt_bound H_edf_policy H_work_conserving

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_completed_by_rt_bound in
theorem interference_bound_edf_holds_for_single_job_that_completes_on_time :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta ≤
      the_D_i task_deadline tsk_i - (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) := by
  sorry

end ResponseTimeOfSingleJobBounded

section ResponseTimeOfSingleJobNotBounded

variable (H_j_fst_not_complete_by_rt_bound :
  let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
  let a_fst := job_arrival j_fst
  ¬ completed job_cost sched j_fst (a_fst + the_J_k task_jitter tsk_k + R_k))

include H_j_fst_not_complete_by_rt_bound H_tsk_i_in_task_set H_delta_le_deadline
  H_edf_policy H_work_conserving

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_not_complete_by_rt_bound in
theorem interference_bound_edf_response_time_bound_of_j_fst_after_interval :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    job_arrival j_fst + the_J_k task_jitter tsk_k + R_k ≥
      job_arrival j_i + the_J_i task_jitter tsk_i + delta := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_not_complete_by_rt_bound in
theorem interference_bound_edf_holds_for_single_job_with_big_slack :
    the_D_i task_deadline tsk_i < the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k →
    the_icb job_arrival job_cost job_jitter sched j_i
      ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem) delta = 0 := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job H_j_fst_not_complete_by_rt_bound in
theorem interference_bound_edf_holds_for_single_job_with_small_slack :
    the_D_i task_deadline tsk_i ≥ the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k →
    the_icb job_arrival job_cost job_jitter sched j_i
      ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem) delta ≤
      the_D_i task_deadline tsk_i - (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) := by
  sorry

end ResponseTimeOfSingleJobNotBounded

include H_edf_policy H_work_conserving H_tsk_i_in_task_set H_delta_le_deadline

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job in
theorem interference_bound_edf_interference_of_j_fst_limited_by_slack :
    the_icb job_arrival job_cost job_jitter sched j_i
      ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem) delta ≤
      the_D_i task_deadline tsk_i - (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_only_one_job in
theorem interference_bound_edf_holds_for_a_single_job :
    the_icb job_arrival job_cost job_jitter sched j_i
      ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem) delta ≤
      the_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  sorry

end InterferenceSingleJob

section InterferenceTwoOrMoreJobs

variable (num_mid_jobs : ℕ)
variable (H_at_least_two_jobs :
  (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).length =
    num_mid_jobs + 2)

include H_many_jobs H_valid_task_parameters H_tsk_k_in_task_set
  H_constrained_deadlines H_R_k_le_deadline H_j_i_arrives H_job_of_tsk_i
  H_all_previous_jobs_completed_on_time H_sporadic_tasks
  H_edf_policy H_work_conserving H_tsk_i_in_task_set H_delta_le_deadline
  H_at_least_two_jobs H_jobs_execute_after_jitter H_at_least_one_cpu

section FactsAboutFirstAndLastJobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_lst_is_job_of_tsk_k :
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    arrives_in arr_seq j_lst ∧
    job_task j_lst = tsk_k ∧
    the_icb job_arrival job_cost job_jitter sched j_i j_lst delta ≠ 0 ∧
    j_lst ∈ jobs_scheduled_between sched
      (the_t1 job_arrival job_jitter j_i) (the_t2 job_arrival job_jitter j_i delta) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_lst_deadline :
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    job_deadline j_lst = task_deadline tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_fst_before_j_lst :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    job_arrival j_fst ≤ job_arrival j_lst := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_last_job_arrives_before_end_of_interval :
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    job_arrival j_lst < the_t2 job_arrival job_jitter j_i delta := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_j_fst_completed_on_time :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let a_fst := job_arrival j_fst
    completed job_cost sched j_fst (a_fst + the_J_k task_jitter tsk_k + R_k) := by
  sorry

end FactsAboutFirstAndLastJobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_many_periods_in_between :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    let a_fst := job_arrival j_fst
    let a_lst := job_arrival j_lst
    a_lst - a_fst ≥ (num_mid_jobs + 1) * the_p_k task_period tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_n_k_covers_middle_jobs_plus_one :
    the_n_k task_deadline task_period tsk_i tsk_k ≥ num_mid_jobs + 1 := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_holds_for_middle_and_last_jobs :
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    the_icb job_arrival job_cost job_jitter sched j_i j_lst delta +
    ∑ i ∈ Finset.Ico 0 num_mid_jobs,
      the_icb job_arrival job_cost job_jitter sched j_i
        ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (i + 1) elem) delta ≤
      the_n_k task_deadline task_period tsk_i tsk_k * task_cost tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_n_k_equals_num_mid_jobs_plus_one :
    the_n_k task_deadline task_period tsk_i tsk_k = num_mid_jobs + 1 := by
  sorry

section InterferenceOfFirstJob

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_remainder_ge_slack :
    the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k ≤
      the_D_i task_deadline tsk_i % the_p_k task_period tsk_k := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_simpl_by_moving_to_left_side :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta +
      (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) +
      the_D_i task_deadline tsk_i / the_p_k task_period tsk_k * the_p_k task_period tsk_k ≤
      the_D_i task_deadline tsk_i →
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta ≤
      the_D_i task_deadline tsk_i % the_p_k task_period tsk_k -
        (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_interference_of_j_fst_bounded_by_response_time :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let a_fst := job_arrival j_fst
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta ≤
      a_fst + the_J_k task_jitter tsk_k + R_k - the_t1 job_arrival job_jitter j_i := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_bounding_interference_with_interval_lengths :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    let a_fst := job_arrival j_fst
    let a_lst := job_arrival j_lst
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta +
      (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) +
      the_D_i task_deadline tsk_i / the_p_k task_period tsk_k * the_p_k task_period tsk_k ≤
      (a_fst + the_J_k task_jitter tsk_k + R_k - the_t1 job_arrival job_jitter j_i) +
      (a_fst + the_D_k task_deadline tsk_k - (a_fst + the_J_k task_jitter tsk_k + R_k)) +
      (a_lst + the_D_k task_deadline tsk_k - (a_fst + the_D_k task_deadline tsk_k)) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_simpl_by_concatenation_of_intervals :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    let j_lst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD (num_mid_jobs + 1) elem
    let a_fst := job_arrival j_fst
    let a_lst := job_arrival j_lst
    (a_fst + the_J_k task_jitter tsk_k + R_k - the_t1 job_arrival job_jitter j_i) +
    (a_fst + the_D_k task_deadline tsk_k - (a_fst + the_J_k task_jitter tsk_k + R_k)) +
    (a_lst + the_D_k task_deadline tsk_k - (a_fst + the_D_k task_deadline tsk_k)) =
      a_lst + the_D_k task_deadline tsk_k - the_t1 job_arrival job_jitter j_i := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack :
    let j_fst := (the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD 0 elem
    the_icb job_arrival job_cost job_jitter sched j_i j_fst delta ≤
      the_D_i task_deadline tsk_i % the_p_k task_period tsk_k -
        (the_D_k task_deadline tsk_k - R_k - the_J_k task_jitter tsk_k) := by
  sorry

end InterferenceOfFirstJob

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs H_at_least_two_jobs in
theorem interference_bound_edf_holds_for_multiple_jobs :
    ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2),
      the_icb job_arrival job_cost job_jitter sched j_i
        ((the_sorted job_arrival job_cost job_task job_jitter sched j_i tsk_k delta).getD i elem) delta ≤
      the_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  sorry

end InterferenceTwoOrMoreJobs

end InterferenceManyJobs

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence
  H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs
  H_at_least_one_cpu H_valid_task_parameters H_constrained_deadlines
  H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives
  H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline
  H_all_previous_jobs_completed_on_time H_all_jobs_from_taskset

include H_sporadic_tasks H_valid_job_parameters H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu H_all_jobs_from_taskset H_valid_task_parameters H_constrained_deadlines H_work_conserving H_edf_policy H_tsk_i_in_task_set H_j_i_arrives H_job_of_tsk_i H_tsk_k_in_task_set H_R_k_le_deadline H_delta_le_deadline H_all_previous_jobs_completed_on_time in
theorem interference_bound_edf_bounds_interference :
    the_x job_arrival job_cost job_task job_jitter sched j_i tsk_k delta ≤
      the_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  sorry

end MainProof

end ProofSpecificBound

section MonotonicitySpecificBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable (tsk tsk_other : sporadic_task)
variable (H_period_positive : task_period tsk_other > 0)

variable (delta delta' R R' : Time)
variable (H_delta_monotonic : delta ≤ delta')
variable (H_response_time_monotonic : R ≤ R')
variable (H_cost_le_rt_bound : task_cost tsk_other ≤ R)

include H_period_positive H_delta_monotonic H_response_time_monotonic H_cost_le_rt_bound

include H_period_positive H_delta_monotonic H_response_time_monotonic H_cost_le_rt_bound in
theorem interference_bound_edf_monotonic :
    interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta (tsk_other, R) ≤
      interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta' (tsk_other, R') := by
  sorry

end MonotonicitySpecificBound

end InterferenceBoundEDFJitter

end Prosa.Classic.Analysis.Global.Jitter.Interference_bound_edf
