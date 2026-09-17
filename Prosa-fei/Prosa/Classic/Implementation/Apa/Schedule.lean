-- Translated from: ../rt-proofs/classic/implementation/apa/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Global.Transformation.Construction
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Implementation.Apa.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Transformation.Construction
open Prosa.Classic.Util.List
open Schedule ScheduleOfSporadicTask ScheduleConstruction

namespace ConcreteScheduler

section Platform
variable {Job : Type _} [DecidableEq Job]
variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (job_arrival : Job → Time) (job_cost : Job → Time) (job_task : Job → sporadic_task)
variable {num_cpus : ℕ} (arr_seq : arrival_sequence Job) (sched_p : schedule Job num_cpus)
variable (alpha : task_affinity sporadic_task num_cpus)

def apa_work_conserving := ∀ (j : Job) (t : Time), arrives_in arr_seq j →
  backlogged job_arrival job_cost sched_p j t → ∀ (cpu : processor num_cpus),
    can_execute_on alpha (job_task j) cpu → ∃ j_other : Job, scheduled_on sched_p j_other cpu t = true

def respects_affinity := ∀ (j : Job) (cpu : processor num_cpus) (t : Time),
  scheduled_on sched_p j cpu t = true → can_execute_on alpha (job_task j) cpu

variable (higher_eq_priority : JLDP_policy Job)

def respects_JLDP_policy_under_weak_APA := ∀ (j j_hp : Job) (cpu : processor num_cpus) (t : Time),
  arrives_in arr_seq j → backlogged job_arrival job_cost sched_p j t →
  scheduled_on sched_p j_hp cpu t = true → can_execute_on alpha (job_task j) cpu →
  higher_eq_priority t j_hp j = true
end Platform

section Implementation
variable {Job : Type _} [DecidableEq Job]
variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (job_arrival : Job → Time) (job_cost : Job → Time) (job_task : Job → sporadic_task)
variable {num_cpus : ℕ} (arr_seq : arrival_sequence Job)
variable (alpha : task_affinity sporadic_task num_cpus) (higher_eq_priority : JLDP_policy Job)

def is_pending (sched_prefix : schedule Job num_cpus) (j : Job) (t : Time) : Bool :=
  decide (job_arrival j ≤ t) && !decide (service sched_prefix j t ≥ job_cost j)

def pending_jobs (sched_prefix : schedule Job num_cpus) (t : Time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun j => is_pending job_arrival job_cost sched_prefix j t)

def sorted_pending_jobs (sched_prefix : schedule Job num_cpus) (t : Time) : List Job :=
  (pending_jobs job_arrival job_cost arr_seq sched_prefix t).mergeSort (fun a b => higher_eq_priority t a b)

def should_be_scheduled (t : Time) (j : Job) (p : processor num_cpus × Option Job) : Bool :=
  match p.2 with
  | some j' => (decide (p.1 ∈ alpha (job_task j))) && !(higher_eq_priority t j' j)
  | none => decide (p.1 ∈ alpha (job_task j))

def update_available_cpu (t : Time) (allocation : List (processor num_cpus × Option Job))
    (j : Job) : List (processor num_cpus × Option Job) :=
  replace_first (should_be_scheduled job_task alpha higher_eq_priority t j) (set_pair_2nd (some j)) allocation

def empty_mapping_ : List (processor num_cpus × Option Job) :=
  (List.finRange num_cpus).zip (List.replicate num_cpus none)

def schedule_jobs_from_list (t : Time) (l : List Job) : List (processor num_cpus × Option Job) :=
  l.foldl (update_available_cpu job_task alpha higher_eq_priority t) (empty_mapping_ (num_cpus := num_cpus))

def apa_schedule (sched_prefix : schedule Job num_cpus) (t : Time) (cpu : processor num_cpus) : Option Job :=
  pairs_to_function none (schedule_jobs_from_list job_task alpha higher_eq_priority t
    (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched_prefix t)) cpu

noncomputable def scheduler : schedule Job num_cpus :=
  build_schedule_from_prefixes
    (fun (pfx : schedule Job num_cpus) (cpu : processor num_cpus) (t : Time) =>
      apa_schedule job_arrival job_cost job_task arr_seq alpha higher_eq_priority pfx t cpu)
    (fun (_ : processor num_cpus) (_ : Time) => (none : Option Job))

theorem scheduler_depends_only_on_prefix (sched1 sched2 : schedule Job num_cpus) (cpu : processor num_cpus) (t : Time)
    (ALL : ∀ (t0 : Time) (cpu0 : processor num_cpus), t0 < t → sched1 cpu0 t0 = sched2 cpu0 t0) :
    apa_schedule job_arrival job_cost job_task arr_seq alpha higher_eq_priority sched1 t cpu =
    apa_schedule job_arrival job_cost job_task arr_seq alpha higher_eq_priority sched2 t cpu := by
  simp only [apa_schedule]
  suffices h : sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched1 t =
    sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched2 t by rw [h]
  simp only [sorted_pending_jobs]
  suffices h : pending_jobs job_arrival job_cost arr_seq sched1 t =
    pending_jobs job_arrival job_cost arr_seq sched2 t by rw [h]
  simp only [pending_jobs]
  apply List.filter_congr
  intro j _
  have SERV_EQ : service sched1 j t = service sched2 j t := by
    simp only [service]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    simp only [service_at, scheduled_on]
    apply Finset.sum_congr rfl
    intro cpu' _
    have := ALL i cpu' hi.2
    simp [this]
  simp only [is_pending, SERV_EQ]

theorem scheduler_uses_construction_function (t : Time) (cpu : processor num_cpus) :
    scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority cpu t =
    apa_schedule job_arrival job_cost job_task arr_seq alpha higher_eq_priority
      (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t cpu := by
  unfold scheduler
  rw [prefix_dependent_schedule_construction]
  intro sched1' sched2' cpu' t' ALL'
  exact scheduler_depends_only_on_prefix job_arrival job_cost job_task arr_seq alpha higher_eq_priority sched1' sched2' cpu' t' ALL'
end Implementation

section Proofs
variable {Job : Type _} [DecidableEq Job]
variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (job_arrival : Job → Time) (job_cost : Job → Time) (job_task : Job → sporadic_task)
variable {num_cpus : ℕ} (H_at_least_one_cpu : num_cpus > 0)
variable (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_transitive : JLDP_is_transitive higher_eq_priority)
variable (H_priority_total : ∀ (t : Time), ∀ (x y : Job), higher_eq_priority t x y = true ∨ higher_eq_priority t y x = true)

section HelperLemmas

theorem scheduler_uniq_cpus (t : Time) (l : List Job) :
    ((schedule_jobs_from_list job_task alpha higher_eq_priority t l).unzip.1).Nodup := by
  unfold schedule_jobs_from_list
  have hpres : ∀ (acc : List (processor num_cpus × Option Job)) (j' : Job),
      (replace_first (should_be_scheduled job_task alpha higher_eq_priority t j')
        (set_pair_2nd (some j')) acc).unzip.1 = acc.unzip.1 := by
    intro acc j'; induction acc with
    | nil => simp [replace_first]
    | cons a tl ih =>
      simp only [replace_first]; split
      · simp [set_pair_2nd, List.unzip_fst]
      · rw [List.unzip_fst, List.map_cons, List.unzip_fst, List.map_cons]
        congr 1; rw [← List.unzip_fst, ← List.unzip_fst]; exact ih
  suffices h : ∀ (acc : List (processor num_cpus × Option Job)),
      acc.unzip.1.Nodup →
      (l.foldl (update_available_cpu job_task alpha higher_eq_priority t) acc).unzip.1.Nodup by
    apply h; unfold empty_mapping_
    rw [List.unzip_fst, List.map_fst_zip]
    exact List.nodup_finRange num_cpus
    simp [List.length_finRange, List.length_replicate]
  intro acc hacc; induction l generalizing acc with
  | nil => exact hacc
  | cons j' tl ih =>
    simp only [List.foldl]; apply ih
    unfold update_available_cpu; rw [hpres]; exact hacc

theorem scheduler_job_in_mapping (l : List Job) (j : Job) (t : Time) (cpu : processor num_cpus) :
    (cpu, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l → j ∈ l := by
  intro SOME
  induction l using List.reverseRecOn with
  | nil =>
    simp only [schedule_jobs_from_list, List.foldl, empty_mapping_] at SOME
    rw [List.mem_iff_getElem] at SOME
    obtain ⟨i, hi, hget⟩ := SOME
    rw [List.getElem_zip] at hget
    exact absurd (Prod.mk.inj hget).2 (by simp [List.getElem_replicate])
  | append_singleton l' j_last ih =>
    unfold schedule_jobs_from_list at SOME ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at SOME
    unfold update_available_cpu at SOME
    rcases replace_first_cases SOME with h | ⟨y, heq, _, _⟩
    · exact List.mem_append_left _ (ih h)
    · simp [set_pair_2nd] at heq
      exact List.mem_append_right _ (heq.2 ▸ List.mem_cons_self)

theorem scheduler_mapping_respects_affinity (j : Job) (t : Time) (cpu : processor num_cpus) :
    (cpu, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t
      (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
        (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t) →
    can_execute_on alpha (job_task j) cpu := by
  intro SOME
  suffices h : ∀ (l : List Job), (cpu, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l →
      can_execute_on alpha (job_task j) cpu from h _ SOME
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro SOME'
    simp only [schedule_jobs_from_list, List.foldl, empty_mapping_] at SOME'
    rw [List.mem_iff_getElem] at SOME'
    obtain ⟨i, hi, hget⟩ := SOME'
    rw [List.getElem_zip] at hget
    exact absurd (Prod.mk.inj hget).2 (by simp [List.getElem_replicate])
  | append_singleton l' j_last ih =>
    intro SOME'
    unfold schedule_jobs_from_list at SOME'
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at SOME'
    unfold update_available_cpu at SOME'
    rcases replace_first_cases SOME' with h | ⟨y, heq, hpy, _⟩
    · exact ih h
    · simp [set_pair_2nd] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [should_be_scheduled] at hpy
      cases hy2 : y.2 with
      | some j' =>
        rw [hy2] at hpy
        simp [can_execute_on] at hpy ⊢
        exact hpy.1
      | none =>
        rw [hy2] at hpy
        simp [can_execute_on] at hpy ⊢
        exact hpy

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem scheduler_has_no_duplicate_jobs (j : Job) (t : Time) (cpu1 cpu2 : processor num_cpus) :
    (cpu1, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t
      (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
        (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t) →
    (cpu2, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t
      (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
        (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t) →
    cpu1 = cpu2 := by
  suffices h : ∀ (l : List Job), l.Nodup →
      (cpu1, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l →
      (cpu2, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l →
      cpu1 = cpu2 by
    exact h _ (by
      unfold sorted_pending_jobs pending_jobs
      rw [List.Perm.nodup_iff (List.mergeSort_perm _ _)]
      exact List.Nodup.filter _
        (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
          H_arrival_sequence_is_a_set 0 (t + 1)))
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _ h1 _
    simp only [schedule_jobs_from_list, List.foldl, empty_mapping_] at h1
    rw [List.mem_iff_getElem] at h1
    obtain ⟨i, hi, hget⟩ := h1
    rw [List.getElem_zip] at hget
    exact absurd (Prod.mk.inj hget).2 (by simp [List.getElem_replicate])
  | append_singleton l' j_last ih =>
    intro UNIQ h1 h2
    have NOTIN : j_last ∉ l' := by
      intro hmem
      exact List.disjoint_of_nodup_append UNIQ hmem (List.mem_cons_self (a := j_last))
    have UNIQ' := (List.nodup_append.mp UNIQ).1
    have hfold : schedule_jobs_from_list job_task alpha higher_eq_priority t (l' ++ [j_last]) =
        replace_first (should_be_scheduled job_task alpha higher_eq_priority t j_last)
          (set_pair_2nd (some j_last))
          (schedule_jobs_from_list job_task alpha higher_eq_priority t l') := by
      simp only [schedule_jobs_from_list, List.foldl_append, List.foldl_cons, List.foldl_nil,
        update_available_cpu]
    rw [hfold] at h1 h2
    have hrc1 := replace_first_cases h1
    have hrc2 := replace_first_cases h2
    rcases hrc1 with h1a | ⟨y1, heq1, _, hy1⟩ <;>
    rcases hrc2 with h2a | ⟨y2, heq2, _, hy2⟩
    · -- Both in prev: use IH
      exact ih UNIQ' h1a h2a
    · -- h1 in prev, h2 from replacement
      simp [set_pair_2nd] at heq2
      have hmem := scheduler_job_in_mapping job_task alpha higher_eq_priority l' j t cpu1 h1a
      rw [heq2.2] at hmem
      exact absurd hmem NOTIN
    · -- h1 from replacement, h2 in prev
      simp [set_pair_2nd] at heq1
      have hmem := scheduler_job_in_mapping job_task alpha higher_eq_priority l' j t cpu2 h2a
      rw [heq1.2] at hmem
      exact absurd hmem NOTIN
    · -- Both from replacement: use replace_first_new
      simp [set_pair_2nd] at heq1 heq2
      have hni1 : (cpu1, some j) ∉ schedule_jobs_from_list job_task alpha higher_eq_priority t l' := by
        intro hmem
        have := scheduler_job_in_mapping job_task alpha higher_eq_priority l' j t cpu1 hmem
        rw [heq1.2] at this
        exact absurd this NOTIN
      have hni2 : (cpu2, some j) ∉ schedule_jobs_from_list job_task alpha higher_eq_priority t l' := by
        intro hmem
        have := scheduler_job_in_mapping job_task alpha higher_eq_priority l' j t cpu2 hmem
        rw [heq2.2] at this
        exact absurd this NOTIN
      exact congr_arg Prod.fst (replace_first_new _ _ _ _ _ hni1 hni2 h1 h2)

theorem scheduler_scheduled_on (j : Job) (cpu : processor num_cpus) (t : Time) :
    scheduled_on (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j cpu t =
    decide ((cpu, some j) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t
      (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
        (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t)) := by
  simp only [scheduled_on]
  rw [scheduler_uses_construction_function job_arrival job_cost job_task arr_seq alpha higher_eq_priority t cpu]
  simp only [apa_schedule]
  set mapping := schedule_jobs_from_list job_task alpha higher_eq_priority t
    (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
      (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t)
  have UNIQ_CPUS := scheduler_uniq_cpus job_task alpha higher_eq_priority t
    (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
      (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t)
  show (pairs_to_function none mapping cpu == some j) = decide ((cpu, some j) ∈ mapping)
  apply Bool.eq_iff_iff.mpr; constructor
  · intro h
    have heq := eq_of_beq h
    have hmem := pairs_to_function_neq_default none mapping cpu (some j) heq (by simp)
    exact decide_eq_true hmem
  · intro hmem
    have hmem' := of_decide_eq_true hmem
    have := pairs_to_function_mem none mapping cpu (some j) UNIQ_CPUS hmem'
    exact beq_iff_eq.mpr this

theorem scheduler_has_cpus (cpu : processor num_cpus) (t : Time) (l : List Job) :
    ∃ x, (cpu, x) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l := by
  unfold schedule_jobs_from_list
  suffices h : ∀ (acc : List (processor num_cpus × Option Job)),
      (∃ x, (cpu, x) ∈ acc) →
      ∃ x, (cpu, x) ∈ l.foldl (update_available_cpu job_task alpha higher_eq_priority t) acc by
    apply h
    refine ⟨none, ?_⟩
    unfold empty_mapping_
    rw [mem_zip_nseq_r _ _ _ _ (by simp [List.length_finRange])]
    exact List.mem_finRange cpu
  intro acc ⟨x, hx⟩; induction l generalizing acc x with
  | nil => exact ⟨x, hx⟩
  | cons j' tl ih =>
    simp only [List.foldl]
    have hprev := @replace_first_previous _ _ (should_be_scheduled job_task alpha higher_eq_priority t j')
      (set_pair_2nd (some j')) acc (cpu, x) hx
    rcases hprev with h1 | ⟨hpx, h2⟩
    · exact ih _ _ h1
    · exact ih _ _ h2

include H_priority_transitive in
theorem scheduler_mapping_is_work_conserving (j : Job) (cpu : processor num_cpus) (t : Time) (l : List Job) :
    j ∈ l → List.IsChain (fun a b => higher_eq_priority t a b = true) l → l.Nodup →
    (∀ (cpu' : processor num_cpus), (cpu', some j) ∉ schedule_jobs_from_list job_task alpha higher_eq_priority t l) →
    can_execute_on alpha (job_task j) cpu →
    ∃ j_other : Job, (cpu, some j_other) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l := by
  intro IN SORT UNIQ NOTSCHED CAN
  induction l using List.reverseRecOn generalizing cpu with
  | nil => simp at IN
  | append_singleton l' j_last ih =>
    have NOTIN : j_last ∉ l' := by
      intro hmem
      exact List.disjoint_of_nodup_append UNIQ hmem (List.mem_cons_self (a := j_last))
    have UNIQ' := (List.nodup_append.mp UNIQ).1
    have hfold : schedule_jobs_from_list job_task alpha higher_eq_priority t (l' ++ [j_last]) =
        replace_first (should_be_scheduled job_task alpha higher_eq_priority t j_last)
          (set_pair_2nd (some j_last))
          (schedule_jobs_from_list job_task alpha higher_eq_priority t l') := by
      simp only [schedule_jobs_from_list, List.foldl_append, List.foldl_cons, List.foldl_nil,
        update_available_cpu]
    rw [hfold] at NOTSCHED ⊢
    rw [List.mem_append, List.mem_singleton] at IN
    rcases IN with IN | rfl
    · -- j ∈ l' (not the last element)
      have SORT' : List.IsChain (fun a b => higher_eq_priority t a b = true) l' :=
        Prosa.Classic.Util.Sorting.sorted_rcons_prefix _ _ j_last SORT
      have NOTSCHED' : ∀ cpu', (cpu', some j) ∉ schedule_jobs_from_list job_task alpha higher_eq_priority t l' := by
        intro cpu' hmem
        rcases replace_first_previous hmem with h1 | ⟨hpy, h2⟩
        · exact NOTSCHED cpu' h1
        · simp only [should_be_scheduled, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hpy
          rcases hpy with ⟨_, hpri⟩
          have hord := Prosa.Classic.Util.Sorting.order_sorted_rcons _ _ j j_last
            (H_priority_transitive t) SORT IN
          rw [hord] at hpri
          exact Bool.noConfusion hpri
      obtain ⟨j_old, hmem⟩ := ih cpu IN SORT' UNIQ' NOTSCHED' CAN
      rcases replace_first_previous hmem with h1 | ⟨_, h2⟩
      · exact ⟨j_old, h1⟩
      · simp [set_pair_2nd] at h2
        exact ⟨j_last, h2⟩
    · -- j = j_last (is the last element)
      have ALL : ∀ x, x ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l' →
          (should_be_scheduled job_task alpha higher_eq_priority t j) x = false := by
        apply replace_first_failed
        intro ⟨cpu', y⟩ hmem habs
        exact NOTSCHED cpu' habs
      obtain ⟨x, hx⟩ := scheduler_has_cpus job_task alpha higher_eq_priority cpu t l'
      have hfail := ALL (cpu, x) hx
      cases x with
      | none =>
        simp [should_be_scheduled, can_execute_on] at hfail
        exact absurd CAN hfail
      | some j' =>
        rcases replace_first_previous hx with h1 | ⟨_, h2⟩
        · exact ⟨j', h1⟩
        · simp [set_pair_2nd] at h2
          exact ⟨j, h2⟩

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_priority_transitive H_priority_total in
theorem scheduler_priority (j j_hp : Job) (cpu : processor num_cpus) (t : Time) :
    arrives_in arr_seq j →
    backlogged job_arrival job_cost (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j t →
    can_execute_on alpha (job_task j) cpu →
    scheduled_on (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j_hp cpu t = true →
    higher_eq_priority t j_hp j = true := by
  intro ARRj BACK CAN SCHED
  set sched := scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority
  obtain ⟨PENDING, NOTSCHED'⟩ := BACK
  have NOTSCHED : ∀ cpu', (cpu', some j) ∉
      schedule_jobs_from_list job_task alpha higher_eq_priority t
        (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched t) := by
    intro cpu' hmem; apply NOTSCHED'
    exact ⟨cpu', by rw [scheduler_scheduled_on]; exact decide_eq_true_eq.mpr hmem⟩
  rw [scheduler_scheduled_on] at SCHED
  simp only [decide_eq_true_eq] at SCHED
  set l := sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched t with hl_def
  have IN : j ∈ l := by
    simp only [sorted_pending_jobs, List.mem_mergeSort, hl_def]
    simp only [pending_jobs, List.mem_filter]
    refine ⟨?_, ?_⟩
    · exact arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent j 0 (t + 1) ARRj
        ⟨Nat.zero_le _, Nat.lt_succ_of_le PENDING.1⟩
    · simp only [is_pending, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le]
      exact ⟨PENDING.1, by have := PENDING.2; simp only [completed, not_le] at this; exact this⟩
  have INhp : j_hp ∈ l := scheduler_job_in_mapping job_task alpha higher_eq_priority _ j_hp t cpu SCHED
  have SORT : List.IsChain (fun a b => higher_eq_priority t a b = true) l := by
    apply List.Pairwise.isChain
    exact List.pairwise_mergeSort (fun a b c => H_priority_transitive t b a c)
      (fun a b => by
        rcases H_priority_total t a b with h | h
        · simp [h]
        · simp [h, Bool.or_true]) _
  have UNIQ : l.Nodup := by
    simp only [sorted_pending_jobs, hl_def]
    rw [List.Perm.nodup_iff (List.mergeSort_perm _ _)]
    exact List.Nodup.filter _
      (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
        H_arrival_sequence_is_a_set 0 (t + 1))
  -- Now prove by reverse induction on l
  suffices h : ∀ (l : List Job), l.Nodup →
      List.IsChain (fun a b => higher_eq_priority t a b = true) l →
      j ∈ l → j_hp ∈ l →
      (∀ cpu', (cpu', some j) ∉ schedule_jobs_from_list job_task alpha higher_eq_priority t l) →
      (cpu, some j_hp) ∈ schedule_jobs_from_list job_task alpha higher_eq_priority t l →
      higher_eq_priority t j_hp j = true by
    exact h l UNIQ SORT IN INhp NOTSCHED SCHED
  intro l'
  induction l' using List.reverseRecOn with
  | nil =>
    intro _ _ _ _ _ h
    simp only [schedule_jobs_from_list, List.foldl, empty_mapping_] at h
    rw [List.mem_iff_getElem] at h
    obtain ⟨i, hi, hget⟩ := h
    rw [List.getElem_zip] at hget
    exact absurd (Prod.mk.inj hget).2 (by simp [List.getElem_replicate])
  | append_singleton xs x ih =>
    intro UNIQ' SORT' IN' INhp' NOTSCHED' SCHED'
    have NOTIN : x ∉ xs := by
      intro hmem
      exact List.disjoint_of_nodup_append UNIQ' hmem (List.mem_cons_self (a := x))
    have UNIQ_xs := (List.nodup_append.mp UNIQ').1
    have SORT_xs := Prosa.Classic.Util.Sorting.sorted_rcons_prefix _ _ x SORT'
    have hfold : schedule_jobs_from_list job_task alpha higher_eq_priority t (xs ++ [x]) =
        replace_first (should_be_scheduled job_task alpha higher_eq_priority t x)
          (set_pair_2nd (some x))
          (schedule_jobs_from_list job_task alpha higher_eq_priority t xs) := by
      simp only [schedule_jobs_from_list, List.foldl_append, List.foldl_cons, List.foldl_nil,
        update_available_cpu]
    rw [hfold] at NOTSCHED' SCHED'
    rw [List.mem_append, List.mem_singleton] at IN' INhp'
    rcases IN' with IN_xs | rfl <;> rcases INhp' with INhp_xs | rfl
    · -- j ∈ xs, j_hp ∈ xs
      have NOTSCHED_xs : ∀ cpu', (cpu', some j) ∉
          schedule_jobs_from_list job_task alpha higher_eq_priority t xs := by
        intro cpu' hmem
        rcases replace_first_previous hmem with h1 | ⟨hpy, h2⟩
        · exact NOTSCHED' cpu' h1
        · simp only [should_be_scheduled, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at hpy
          have hord := Prosa.Classic.Util.Sorting.order_sorted_rcons _ _ j x
            (H_priority_transitive t) SORT' IN_xs
          rw [hord] at hpy; exact Bool.noConfusion hpy.2
      rcases replace_first_cases SCHED' with h1 | ⟨y, heq, _, _⟩
      · exact ih UNIQ_xs SORT_xs IN_xs INhp_xs NOTSCHED_xs h1
      · simp [set_pair_2nd] at heq; obtain ⟨_, rfl⟩ := heq
        exact absurd INhp_xs NOTIN
    · -- j ∈ xs, j_hp = x → contradiction via work conservation
      exfalso
      set prev := schedule_jobs_from_list job_task alpha higher_eq_priority t xs with hprev_def
      rcases replace_first_cases SCHED' with h1 | ⟨⟨y_cpu, y_val⟩, heq, hpy, hy_mem⟩
      · -- j_hp was already in prev → contradicts NOTIN
        exact absurd (scheduler_job_in_mapping job_task alpha higher_eq_priority _ j_hp t cpu h1) NOTIN
      · -- j_hp placed by replace_first
        simp [set_pair_2nd] at heq
        subst heq
        cases y_val with
        | some j' =>
          -- should_be_scheduled gives ¬ higher_eq_priority t j' j_hp
          simp [should_be_scheduled] at hpy
          have hord := Prosa.Classic.Util.Sorting.order_sorted_rcons _ _ j' j_hp
            (H_priority_transitive t) SORT'
            (scheduler_job_in_mapping job_task alpha higher_eq_priority _ j' t cpu hy_mem)
          rw [hord] at hpy; exact Bool.noConfusion hpy.2
        | none =>
          -- (cpu, none) ∈ prev; j ∈ xs but j not scheduled after replace_first
          by_cases hj_prev : ∃ cpu'', (cpu'', some j) ∈ prev
          · -- j scheduled in prev → replace_first_previous gives contradiction
            obtain ⟨cpu'', hcpu_mem⟩ := hj_prev
            rcases replace_first_previous hcpu_mem with h_surv | ⟨hpj, _⟩
            · exact NOTSCHED' cpu'' h_surv
            · simp [should_be_scheduled] at hpj
              have hord := Prosa.Classic.Util.Sorting.order_sorted_rcons _ _ j j_hp
                (H_priority_transitive t) SORT' IN_xs
              rw [hord] at hpj; exact Bool.noConfusion hpj.2
          · -- j not scheduled in prev → work conservation gives (cpu, some j_other) ∈ prev
            push_neg at hj_prev
            obtain ⟨j_other, hj_other⟩ := scheduler_mapping_is_work_conserving
              job_task alpha higher_eq_priority (H_priority_transitive := H_priority_transitive)
              j cpu t xs IN_xs SORT_xs UNIQ_xs hj_prev CAN
            -- Both (cpu, none) and (cpu, some j_other) in prev → contradicts CPU uniqueness
            have UCPUS := scheduler_uniq_cpus job_task alpha higher_eq_priority t xs
            have h1 := pairs_to_function_mem none prev cpu none UCPUS hy_mem
            have h2 := pairs_to_function_mem none prev cpu (some j_other) UCPUS hj_other
            simp [h1] at h2
    · -- j = x, j_hp ∈ xs
      rcases replace_first_cases SCHED' with h1 | ⟨y, heq, hpy, _⟩
      · -- j_hp was already placed from xs; priority follows from sorted order
        exact Prosa.Classic.Util.Sorting.order_sorted_rcons _ _ j_hp j
          (H_priority_transitive t) SORT' INhp_xs
      · simp [set_pair_2nd] at heq; obtain ⟨_, rfl⟩ := heq
        -- j_hp was placed as x = j; so NOTSCHED' for cpu contradicts SCHED'
        exfalso; exact NOTSCHED' cpu SCHED'
    · -- j = x, j_hp = x → same job, contradicts NOTSCHED'
      exfalso; exact NOTSCHED' cpu SCHED'
end HelperLemmas

theorem scheduler_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) arr_seq := by
  intro j t ⟨cpu, SCHED⟩
  rw [scheduler_scheduled_on] at SCHED
  simp only [decide_eq_true_eq] at SCHED
  have hmem := scheduler_job_in_mapping job_task alpha higher_eq_priority _ j t cpu SCHED
  simp only [sorted_pending_jobs, List.mem_mergeSort] at hmem
  simp only [pending_jobs, List.mem_filter] at hmem
  obtain ⟨harr, _⟩ := hmem
  have ⟨i, hi_mem, _, _⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists j 0 (t + 1) (jobs_arriving_at arr_seq) harr
  exact ⟨i, hi_mem⟩

theorem scheduler_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) := by
  intro j t ⟨cpu, SCHED⟩
  rw [scheduler_scheduled_on] at SCHED
  simp only [decide_eq_true_eq] at SCHED
  have hmem := scheduler_job_in_mapping job_task alpha higher_eq_priority _ j t cpu SCHED
  simp only [sorted_pending_jobs, List.mem_mergeSort] at hmem
  simp only [pending_jobs, List.mem_filter] at hmem
  obtain ⟨_, hpend⟩ := hmem
  simp only [is_pending, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, not_le] at hpend
  exact hpend.1

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem scheduler_sequential_jobs :
    sequential_jobs (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) := by
  intro j t cpu1 cpu2 SCHED1 SCHED2
  have h1 : scheduled_on (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j cpu1 t = true := by
    simp [scheduled_on, SCHED1]
  have h2 : scheduled_on (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j cpu2 t = true := by
    simp [scheduled_on, SCHED2]
  rw [scheduler_scheduled_on] at h1 h2
  simp only [decide_eq_true_eq] at h1 h2
  exact scheduler_has_no_duplicate_jobs job_arrival job_cost job_task alpha arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority j t cpu1 cpu2 h1 h2

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem scheduler_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) := by
  intro j t
  induction t with
  | zero =>
    unfold service; simp
  | succ t IHt =>
    unfold service
    rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
    by_cases hlt : ∑ t_0 ∈ Finset.Ico 0 t, service_at (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j t_0 < job_cost j
    · have hseq := scheduler_sequential_jobs job_arrival job_cost job_task alpha arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
      have hle1 := service_at_most_one (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j hseq t
      omega
    · push_neg at hlt
      have heq : ∑ t_0 ∈ Finset.Ico 0 t, service_at (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j t_0 = job_cost j := by
        unfold service at IHt
        exact Nat.le_antisymm IHt hlt
      have hnsched : ¬ scheduled (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j t := by
        intro ⟨cpu, hon⟩
        unfold scheduled_on at hon
        have hsched_eq := eq_of_beq hon
        rw [scheduler_uses_construction_function job_arrival job_cost job_task arr_seq alpha higher_eq_priority t cpu] at hsched_eq
        simp only [apa_schedule] at hsched_eq
        have hmem := pairs_to_function_neq_default none
          (schedule_jobs_from_list job_task alpha higher_eq_priority t
            (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
              (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) t)) cpu (some j) hsched_eq (by simp)
        have hmem2 := scheduler_job_in_mapping job_task alpha higher_eq_priority _ j t cpu hmem
        simp only [sorted_pending_jobs, List.mem_mergeSort] at hmem2
        simp only [pending_jobs, List.mem_filter] at hmem2
        obtain ⟨_, hpend⟩ := hmem2
        simp only [is_pending, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not, not_le] at hpend
        have hcomp : completed job_cost (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j t := by
          unfold completed service; omega
        unfold completed at hcomp
        exact absurd hcomp (not_le.mpr hpend.2)
      have hzero := (not_scheduled_no_service (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) j t).mp hnsched
      omega

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_priority_transitive H_priority_total in
theorem scheduler_apa_work_conserving :
    apa_work_conserving job_arrival job_cost job_task arr_seq
      (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) alpha := by
  intro j t ARRj BACK cpu CAN
  set sched := scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority with hsched_def
  set l := sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched t with hl_def
  have SORT : List.IsChain (fun a b => higher_eq_priority t a b = true) l := by
    apply List.Pairwise.isChain
    exact List.pairwise_mergeSort (fun a b c => H_priority_transitive t b a c)
      (fun a b => by
        rcases H_priority_total t a b with h | h
        · simp [h]
        · simp [h, Bool.or_true]) _
  have UNIQ : l.Nodup := by
    simp only [sorted_pending_jobs, hl_def]
    rw [List.Perm.nodup_iff (List.mergeSort_perm _ _)]
    exact List.Nodup.filter _
      (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
        H_arrival_sequence_is_a_set 0 (t + 1))
  obtain ⟨PENDING, NOTSCHED'⟩ := BACK
  have IN : j ∈ l := by
    simp only [sorted_pending_jobs, List.mem_mergeSort, hl_def]
    simp only [pending_jobs, List.mem_filter]
    refine ⟨?_, ?_⟩
    · exact arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent j 0 (t + 1) ARRj
        ⟨Nat.zero_le _, Nat.lt_succ_of_le PENDING.1⟩
    · simp only [is_pending, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le]
      exact ⟨PENDING.1, by
        have := PENDING.2
        simp only [completed, not_le] at this
        exact this⟩
  have NOTSCHED : ∀ cpu', (cpu', some j) ∉
      schedule_jobs_from_list job_task alpha higher_eq_priority t l := by
    intro cpu' hmem
    apply NOTSCHED'
    exact ⟨cpu', by
      rw [scheduler_scheduled_on]
      exact decide_eq_true_eq.mpr hmem⟩
  obtain ⟨j_other, hmem⟩ := scheduler_mapping_is_work_conserving job_task alpha higher_eq_priority
    H_priority_transitive j cpu t l IN SORT UNIQ NOTSCHED CAN
  exact ⟨j_other, by
    rw [scheduler_scheduled_on]
    exact decide_eq_true_eq.mpr hmem⟩

theorem scheduler_respects_affinity :
    respects_affinity job_task (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) alpha := by
  intro j cpu t SCHED
  apply scheduler_mapping_respects_affinity
  rw [scheduler_scheduled_on] at SCHED
  exact decide_eq_true_eq.mp SCHED

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_priority_transitive H_priority_total in
theorem scheduler_respects_policy :
    respects_JLDP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
      (scheduler job_arrival job_cost job_task arr_seq alpha higher_eq_priority) alpha higher_eq_priority := by
  intro j j_hp cpu t ARRj BACK SCHED ALPHA
  exact scheduler_priority job_arrival job_cost job_task alpha arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    H_priority_transitive H_priority_total j j_hp cpu t ARRj BACK ALPHA SCHED

end Proofs

end ConcreteScheduler

end Prosa.Classic.Implementation.Apa.Schedule
