-- Translated from: ../rt-proofs/analysis/facts/model/service_of_jobs.v
import Prosa.Model.Aggregate.Workload
import Prosa.Model.Aggregate.Service_of_jobs
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Facts.Model.Ideal_schedule
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Facts.Model.Service_of_jobs

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Platform_properties
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Model.Processor.Ideal
open Prosa.Model.Task.Concept
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Service

section GenericModelLemmas

variable {Task : TaskType}
variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable {PState : Type _}
variable [ProcessorState Job PState]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule PState)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (P : Job → Bool)

section ServiceBoundedByWorkload

variable (jobs : List Job)

variable (H_unit_service : unit_service_proc_model (Job := Job) PState)

include H_completed_jobs_dont_execute H_unit_service H_arrival_times_are_consistent H_jobs_must_arrive_to_execute in
theorem service_of_jobs_le_workload :
    ∀ t1 t2,
      service_of_jobs sched P jobs t1 t2 ≤ workload_of_jobs P jobs := by
  intro t1 t2
  unfold service_of_jobs workload_of_jobs
  set l := jobs.filter (fun j => P j)
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    apply Nat.add_le_add
    · exact cumulative_service_le_job_cost sched H_completed_jobs_dont_execute a H_unit_service t1 t2
    · exact ih

end ServiceBoundedByWorkload

section ServiceCat

include H_arrival_times_are_consistent H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem service_of_jobs_cat_scheduling_interval :
    ∀ t1 t2 t,
      t1 ≤ t → t ≤ t2 →
      service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t2
      = service_of_jobs sched P (arrivals_between arr_seq t1 t) t1 t
        + service_of_jobs sched P (arrivals_between arr_seq t1 t) t t2
        + service_of_jobs sched P (arrivals_between arr_seq t t2) t t2 := by
  intro t1 t2 t h1 h2
  -- Helper: split time interval for any list of jobs
  have h_list_sum_split : ∀ (L : List Job),
      (L.map (fun j => ∑ t' ∈ Finset.Ico t1 t2, service_at sched j t')).sum =
      (L.map (fun j => ∑ t' ∈ Finset.Ico t1 t, service_at sched j t')).sum +
      (L.map (fun j => ∑ t' ∈ Finset.Ico t t2, service_at sched j t')).sum := by
    intro L; induction L with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]; rw [ih]
      have : ∑ t' ∈ Finset.Ico t1 t2, service_at sched a t' =
          ∑ t' ∈ Finset.Ico t1 t, service_at sched a t' +
          ∑ t' ∈ Finset.Ico t t2, service_at sched a t' := by
        rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive t1 t t2),
            Finset.Ico_union_Ico_eq_Ico h1 h2]
      simp only [work, instant] at *; omega
  -- Split arrivals list and time intervals
  unfold service_of_jobs
  rw [arrivals_between_cat arr_seq t1 t t2 h1 h2, List.filter_append, List.map_append, List.sum_append]
  simp only [service_during]
  rw [h_list_sum_split ((arrivals_between arr_seq t1 t).filter P)]
  rw [h_list_sum_split ((arrivals_between arr_seq t t2).filter P)]
  -- Show cross term: service of jobs arriving in [t, t2) during [t1, t) is 0
  suffices h_zero : (((arrivals_between arr_seq t t2).filter P).map
      (fun j => ∑ t' ∈ Finset.Ico t1 t, service_at sched j t')).sum = 0 by
    simp only [h_zero, Nat.zero_add, work, instant]
  apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have h_between := in_arrivals_implies_arrived_between arr_seq H_arrival_times_are_consistent j t t2
    (List.mem_filter.mp hj).1
  apply Finset.sum_eq_zero; intro i hi; rw [Finset.mem_Ico] at hi
  exact service_before_job_arrival_zero sched j H_jobs_must_arrive_to_execute i
    (lt_of_lt_of_le hi.2 h_between.1)

include H_arrival_times_are_consistent H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem service_of_jobs_cat_arrival_interval :
    ∀ t1 t2 t,
      t1 ≤ t → t ≤ t2 →
      service_of_jobs sched P (arrivals_between arr_seq t1 t2) t t2 =
      service_of_jobs sched P (arrivals_between arr_seq t1 t) t t2 +
      service_of_jobs sched P (arrivals_between arr_seq t t2) t t2 := by
  intro t1 t2 t ht1 ht2
  simp only [service_of_jobs]
  rw [arrivals_between_cat arr_seq t1 t t2 ht1 ht2]
  simp only [List.filter_append, List.map_append, List.sum_append]

end ServiceCat

end GenericModelLemmas

section IdealModelLemmas

variable {Task : TaskType}
variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable [DecidableEq Job]

attribute [local instance] pstate_instance

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (P : Job → Bool)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem low_service_implies_existence_of_idle_time :
    ∀ t1 t2,
      service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 t2) t1 t2 < t2 - t1 →
      ∃ t, t1 ≤ t ∧ t < t2 ∧ is_idle sched t := by
  intro t1 t2 h_serv
  have h_le : t1 ≤ t2 := by simp only [work, instant] at *; omega
  obtain ⟨δ, rfl⟩ : ∃ δ, t2 = t1 + δ := ⟨t2 - t1, (Nat.add_sub_cancel' h_le).symm⟩
  rw [show t1 + δ - t1 = δ from Nat.add_sub_cancel_left t1 δ] at h_serv
  -- Swap sum order: ∑_j ∑_t service_at → ∑_t ∑_j service_at
  unfold service_of_jobs service_during at h_serv
  have h_swap : ∀ (l : List Job),
      (l.map (fun j => ∑ t' ∈ Finset.Ico t1 (t1 + δ), service_at sched j t')).sum =
      ∑ t' ∈ Finset.Ico t1 (t1 + δ), (l.map (fun j => service_at sched j t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
  rw [h_swap] at h_serv
  -- Find time x where inner sum = 0
  obtain ⟨x, hx_ge, hx_lt, hx_zero⟩ := Prosa.Util.Sum.sum_le_summation_range
    (fun t' => ((arrivals_between arr_seq 0 (t1 + δ)).filter (fun _ => true) |>.map (fun j => service_at sched j t')).sum)
    t1 δ h_serv
  use x
  refine ⟨hx_ge, hx_lt, ?_⟩
  -- Show is_idle sched x, i.e., sched x = none
  show sched x = none
  by_contra h_not_idle
  -- sched x is some job s
  obtain ⟨s, hs⟩ : ∃ s, sched x = some s := by
    cases heq : sched x with
    | none => exact absurd heq h_not_idle
    | some j => exact ⟨j, rfl⟩
  -- s is scheduled at x
  have h_sched_s : scheduled_at sched s x = true := by
    rw [scheduled_at_def]; simp [hs]
  -- s comes from arrival sequence and has arrived
  have h_arrives : arrives_in arr_seq s := H_jobs_come_from_arrival_sequence s x h_sched_s
  have h_arr : has_arrived s x := H_jobs_must_arrive_to_execute s x h_sched_s
  -- s ∈ arrivals_between arr_seq 0 (t1 + δ)
  have h_in_arrivals : s ∈ arrivals_between arr_seq 0 (t1 + δ) :=
    arrived_between_implies_in_arrivals arr_seq H_arrival_times_are_consistent s 0 (t1 + δ) h_arrives
      ⟨Nat.zero_le _, Nat.lt_of_le_of_lt (by unfold has_arrived at h_arr; exact h_arr) hx_lt⟩
  -- s passes the filter (fun _ => true)
  have h_in_filtered : s ∈ (arrivals_between arr_seq 0 (t1 + δ)).filter (fun _ => true) := by
    rw [List.mem_filter]; exact ⟨h_in_arrivals, rfl⟩
  -- service_at sched s x = 1
  have h_sa_pos : service_at sched s x = 1 := by
    rw [service_at_is_scheduled_at, scheduled_at_def, hs]; simp
  -- But the sum at x is 0, contradiction
  have h_sa_in_map : service_at sched s x ∈
      ((arrivals_between arr_seq 0 (t1 + δ)).filter (fun _ => true) |>.map (fun j => service_at sched j x)) :=
    List.mem_map.mpr ⟨s, h_in_filtered, rfl⟩
  have h_sa_le : service_at sched s x ≤
      ((arrivals_between arr_seq 0 (t1 + δ)).filter (fun _ => true) |>.map (fun j => service_at sched j x)).sum :=
    List.le_sum_of_mem h_sa_in_map
  simp only [work, instant] at *; omega

section ServiceOfJobsIsBoundedByLength

variable (jobs : List Job)

variable (H_no_duplicate_jobs : jobs.Nodup)

include H_completed_jobs_dont_execute H_no_duplicate_jobs H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute in
theorem service_of_jobs_le_1 :
    ∀ t,
      ((jobs.filter (fun j => P j)).map (fun j => service_at sched j t)).sum ≤ 1 := by
  intro t
  have h_nodup_f := List.Nodup.filter (fun j => P j) H_no_duplicate_jobs
  cases hsched : sched t with
  | none =>
    suffices h : ((jobs.filter (fun j => P j)).map (fun j => service_at sched j t)).sum = 0 by simp only [work] at *; omega
    apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    apply not_scheduled_implies_no_service
    rw [scheduled_at_def, hsched]; simp
  | some j0 =>
    suffices h_le1 : ∀ (l : List Job), l.Nodup →
        (l.map (fun j => service_at sched j t)).sum ≤ 1 from h_le1 _ h_nodup_f
    intro l hl
    induction l with
    | nil => simp
    | cons a l' ih =>
      rw [List.nodup_cons] at hl; simp only [List.map_cons, List.sum_cons]
      by_cases ha : a = j0
      · have h_rest : (l'.map (fun j => service_at sched j t)).sum = 0 := by
          apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          have hne : j ≠ a := fun heq => hl.1 (heq ▸ hj)
          apply not_scheduled_implies_no_service
          rw [scheduled_at_def, hsched]
          exact decide_eq_false (fun heq => hne (ha ▸ (Option.some_injective _ heq.symm)))
        rw [h_rest]
        have : service_at sched a t ≤ 1 := by
          rw [service_at_is_scheduled_at]; split <;> simp_all [work]
        simp only [work] at *; omega
      · have : service_at sched a t = 0 := by
          apply not_scheduled_implies_no_service
          rw [scheduled_at_def, hsched]
          exact decide_eq_false (fun heq => ha (Option.some_injective _ heq.symm))
        rw [this, Nat.zero_add]; exact ih hl.2

include H_completed_jobs_dont_execute H_no_duplicate_jobs H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute in
theorem service_of_jobs_le_length_of_interval :
    ∀ (t : instant) (Δ : duration),
      service_of_jobs sched P jobs t (t + Δ) ≤ Δ := by
  intro t Δ
  unfold service_of_jobs; simp only [service_during]
  have h_swap : ∀ (l : List Job),
      (l.map (fun j => ∑ t' ∈ Finset.Ico t (t + Δ), service_at sched j t')).sum =
      ∑ t' ∈ Finset.Ico t (t + Δ), (l.map (fun j => service_at sched j t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
  rw [h_swap]
  calc ∑ t' ∈ Finset.Ico t (t + Δ), ((jobs.filter (fun j => P j)).map (fun j => service_at sched j t')).sum
      ≤ ∑ _t' ∈ Finset.Ico t (t + Δ), 1 :=
        Finset.sum_le_sum (fun t' _ => service_of_jobs_le_1 arr_seq H_arrival_times_are_consistent
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          P jobs H_no_duplicate_jobs t')
    _ = Δ := by simp [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]

include H_completed_jobs_dont_execute H_no_duplicate_jobs H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute in
theorem service_of_jobs_le_length_of_interval' :
    ∀ (t1 t2 : instant),
      service_of_jobs sched P jobs t1 t2 ≤ t2 - t1 := by
  intro t1 t2
  by_cases h : t1 ≤ t2
  · have hle := service_of_jobs_le_length_of_interval arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      P jobs H_no_duplicate_jobs t1 (t2 - t1)
    rwa [Nat.add_sub_cancel' h] at hle
  · push_neg at h
    have h_empty : Finset.Ico t1 t2 = ∅ := Finset.Ico_eq_empty (by simp only [instant] at *; omega)
    have : service_of_jobs sched P jobs t1 t2 = 0 := by
      unfold service_of_jobs service_during
      apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
      obtain ⟨j, _, rfl⟩ := hx; rw [h_empty, Finset.sum_empty]
    simp only [work, instant] at *; omega

end ServiceOfJobsIsBoundedByLength

section WorkloadServiceAndCompletion

variable (t1 t2 : instant)

variable (t_compl : instant)

include H_arrival_times_are_consistent H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute in
include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem workload_eq_service_impl_all_jobs_have_completed :
    workload_of_jobs P (arrivals_between arr_seq t1 t2) =
    service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t_compl →
    ∀ j, j ∈ arrivals_between arr_seq t1 t2 → P j = true →
      completed_by sched j t_compl := by
  intro hEQ j hmem hPj
  -- From sum equality + majorant, derive service_during = job_cost for j
  have hSD : service_during sched j t1 t_compl = job_cost j := by
    apply Prosa.Util.Sum.sum_majorant_eqn
      (arrivals_between arr_seq t1 t2)
      (fun j => service_during sched j t1 t_compl) (fun j => job_cost j) P
      (fun x _ _ => cumulative_service_le_job_cost sched H_completed_jobs_dont_execute x
        ideal_proc_model_provides_unit_service t1 t_compl)
    · -- sum equality: ∑ service_during = ∑ job_cost
      unfold service_of_jobs workload_of_jobs at hEQ
      exact hEQ.symm
    · exact hmem
    · exact hPj
  -- completed_by means service ≥ job_cost
  unfold completed_by service
  rw [ge_iff_le, ← hSD]
  -- service_during 0 t_compl ≥ service_during t1 t_compl
  simp only [service_during]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ico_subset_Ico (Nat.zero_le t1) le_rfl
  · intro _ _ _; exact Nat.zero_le _

include H_arrival_times_are_consistent H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute in
include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem all_jobs_have_completed_impl_workload_eq_service :
    (∀ j, j ∈ arrivals_between arr_seq t1 t2 → P j = true →
      completed_by sched j t_compl) →
    workload_of_jobs P (arrivals_between arr_seq t1 t2) =
    service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t_compl := by
  intro COMPL
  unfold workload_of_jobs service_of_jobs
  apply Prosa.Util.Sum.eq_sum_seq (arrivals_between arr_seq t1 t2) P
    (fun j => job_cost j) (fun j => service_during sched j t1 t_compl)
  intro a ha hPa
  have hCOMPL := COMPL a ha hPa
  have harr := (in_arrivals_implies_arrived_between arr_seq H_arrival_times_are_consistent a t1 t2 ha)
  have hge_t1 : t1 ≤ job_arrival a := harr.1
  by_cases hle : t1 ≤ t_compl
  · -- Case t1 ≤ t_compl
    have hcat := service_cat sched a t1 t_compl hle
    have hbefore : service sched a t1 = 0 := by
      unfold service
      exact cumulative_service_before_job_arrival_zero sched a H_jobs_must_arrive_to_execute 0 t1 hge_t1
    -- service_during t1 t_compl = service t_compl
    rw [hbefore, Nat.zero_add] at hcat
    -- service t_compl = job_cost
    unfold completed_by at hCOMPL
    have hle_cost := service_at_most_cost sched H_completed_jobs_dont_execute a
      ideal_proc_model_provides_unit_service t_compl
    exact (hcat.trans (le_antisymm hle_cost hCOMPL)).symm
  · -- Case t_compl < t1
    push_neg at hle
    have h1 : service_during sched a t1 t_compl = 0 := by
      unfold service_during
      rw [Finset.Ico_eq_empty_of_le (Nat.le_of_lt hle)]
      simp
    have hge_tc : t_compl ≤ job_arrival a := Nat.le_trans (Nat.le_of_lt hle) hge_t1
    have hbefore := cumulative_service_before_job_arrival_zero sched a H_jobs_must_arrive_to_execute 0 t_compl hge_tc
    unfold completed_by service at hCOMPL
    -- hCOMPL : job_cost a ≤ service_during sched a 0 t_compl
    -- hbefore : service_during sched a 0 t_compl = 0
    rw [hbefore] at hCOMPL
    -- hCOMPL : job_cost a ≤ 0
    have h2 : job_cost a = 0 := le_antisymm hCOMPL (Nat.zero_le _)
    rw [h1, h2]

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute in
theorem all_jobs_have_completed_equiv_workload_eq_service :
    (∀ j, j ∈ arrivals_between arr_seq t1 t2 → P j = true →
      completed_by sched j t_compl) ↔
    workload_of_jobs P (arrivals_between arr_seq t1 t2) =
    service_of_jobs sched P (arrivals_between arr_seq t1 t2) t1 t_compl := by
  exact ⟨all_jobs_have_completed_impl_workload_eq_service arr_seq H_arrival_times_are_consistent
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    P t1 t2 t_compl,
    workload_eq_service_impl_all_jobs_have_completed arr_seq H_arrival_times_are_consistent
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    P t1 t2 t_compl⟩

end WorkloadServiceAndCompletion

end IdealModelLemmas

end Prosa.Analysis.Facts.Model.Service_of_jobs
