-- Translated from: classic/implementation/global/basic/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Transformation.Construction

namespace Prosa.Classic.Implementation.Global.Basic.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.List
open Prosa.Classic.Util.Sorting

namespace ConcreteScheduler

def pending_jobs {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time) {num_cpus : ℕ}
    (arr_seq : arrival_sequence Job) (sched_prefix : schedule Job num_cpus)
    (t : Time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter
    (fun j => (decide (job_arrival j ≤ t)) && !(decide (service sched_prefix j t ≥ job_cost j)))

def sorted_pending_jobs {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time) {num_cpus : ℕ}
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job)
    (sched_prefix : schedule Job num_cpus) (t : Time) : List Job :=
  (pending_jobs job_arrival job_cost arr_seq sched_prefix t).mergeSort
    (higher_eq_priority t)

def nth_highest_priority_job {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time) {num_cpus : ℕ}
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job)
    (sched_prefix : schedule Job num_cpus) (cpu : processor num_cpus)
    (t : Time) : Option Job :=
  nth_or_none
    (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched_prefix t)
    cpu

noncomputable def scheduler {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time) (num_cpus : ℕ)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    schedule Job num_cpus :=
  build_schedule_from_prefixes
    (fun s cpu t => nth_highest_priority_job job_arrival job_cost arr_seq
      higher_eq_priority s cpu t)
    (fun _cpu _t => none)

section Implementation

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (num_cpus : ℕ)
variable (arr_seq : arrival_sequence Job)
variable (higher_eq_priority : JLDP_policy Job)

theorem scheduler_depends_only_on_prefix :
    ∀ (sched1 sched2 : schedule Job num_cpus)
      (cpu : processor num_cpus) (t : Time),
      (∀ t0 (cpu0 : processor num_cpus), t0 < t → sched1 cpu0 t0 = sched2 cpu0 t0) →
      nth_highest_priority_job job_arrival job_cost arr_seq higher_eq_priority
        sched1 cpu t =
      nth_highest_priority_job job_arrival job_cost arr_seq higher_eq_priority
        sched2 cpu t := by
  intro sched1 sched2 cpu t ALL
  unfold nth_highest_priority_job
  suffices SAME : sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched1 t =
    sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched2 t by
    rw [SAME]
  unfold sorted_pending_jobs
  have PEND : pending_jobs job_arrival job_cost arr_seq sched1 t =
    pending_jobs job_arrival job_cost arr_seq sched2 t := by
    unfold pending_jobs
    apply List.filter_congr
    intro j _
    have SERV : service sched1 j t = service sched2 j t := by
      unfold service
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold service_at
      apply Finset.sum_congr rfl
      intro cpu' _
      unfold scheduled_on
      rw [ALL i cpu' hi.2]
    simp only [SERV]
  rw [PEND]

theorem scheduler_uses_construction_function :
    ∀ (t : Time) (cpu : processor num_cpus),
      scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority cpu t =
        nth_highest_priority_job job_arrival job_cost arr_seq higher_eq_priority
          (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) cpu t := by
  intro t cpu
  apply prefix_dependent_schedule_construction
  exact scheduler_depends_only_on_prefix job_arrival job_cost num_cpus arr_seq higher_eq_priority

end Implementation

section Proofs

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (num_cpus : ℕ)
variable (H_at_least_one_cpu : num_cpus > 0)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_transitive : JLDP_is_transitive higher_eq_priority)
variable (H_priority_total : ∀ t, ∀ x y, higher_eq_priority t x y = true ∨ higher_eq_priority t y x = true)

include H_at_least_one_cpu H_arrival_times_are_consistent H_arrival_sequence_is_a_set
        H_priority_transitive H_priority_total

section HelperLemmas

theorem scheduler_nth_or_none_mapping :
    ∀ (t : Time) (cpu : processor num_cpus),
      scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority cpu t =
        nth_or_none
          (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
            (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) cpu := by
  intro t cpu
  exact scheduler_uses_construction_function job_arrival job_cost num_cpus arr_seq higher_eq_priority t cpu

theorem scheduler_nth_or_none_backlogged :
    ∀ (j : Job) (t : Time),
      arrives_in arr_seq j →
      backlogged job_arrival job_cost
        (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j t →
      ∃ i,
        nth_or_none
          (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
            (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) i = some j ∧
          i ≥ num_cpus := by
  intro j t ARRj BACK
  set sched := scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority
  set sorted_jobs := sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority sched t
  obtain ⟨PENDING, NOTCOMP⟩ := BACK
  have IN : j ∈ sorted_jobs := by
    show j ∈ (pending_jobs job_arrival job_cost arr_seq sched t).mergeSort (higher_eq_priority t)
    rw [List.mem_mergeSort]
    unfold pending_jobs
    rw [List.mem_filter]
    obtain ⟨harr, hnotcomp⟩ := PENDING
    constructor
    · exact arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent j 0 (t + 1) ARRj
        ⟨Nat.zero_le _, Nat.lt_succ_of_le harr⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, not_le]
      constructor
      · exact harr
      · unfold completed at hnotcomp
        exact Nat.not_le.mp hnotcomp
  obtain ⟨n, hn⟩ := nth_or_none_mem_exists sorted_jobs j IN
  exact ⟨n, hn, by
    by_contra hlt
    push_neg at hlt
    apply NOTCOMP
    exact ⟨⟨n, hlt⟩, by
      unfold scheduled_on
      change (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority ⟨n, hlt⟩ t == some j) = true
      rw [scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
        H_priority_transitive H_priority_total t ⟨n, hlt⟩]
      show (nth_or_none (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
        (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) n == some j) = true
      rw [hn]; exact beq_self_eq_true _⟩⟩

end HelperLemmas

theorem scheduler_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) arr_seq := by
  intro j t ⟨cpu, SCHED⟩
  have SCHED' := SCHED
  unfold scheduled_on at SCHED'
  rw [scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    H_priority_transitive H_priority_total t cpu] at SCHED'
  have SCHED'' : nth_or_none (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
    (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) cpu = some j := by
    exact eq_of_beq SCHED'
  have MEM := nth_or_none_mem _ _ _ SCHED''
  unfold sorted_pending_jobs at MEM
  rw [List.mem_mergeSort] at MEM
  unfold pending_jobs at MEM
  rw [List.mem_filter] at MEM
  obtain ⟨ARR, _⟩ := MEM
  exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) ARR

theorem scheduler_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) := by
  intro j t ⟨cpu, SCHED⟩
  have SCHED' := SCHED
  unfold scheduled_on at SCHED'
  rw [scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    H_priority_transitive H_priority_total t cpu] at SCHED'
  have SCHED'' : nth_or_none (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
    (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) cpu = some j :=
    eq_of_beq SCHED'
  have MEM := nth_or_none_mem _ _ _ SCHED''
  unfold sorted_pending_jobs at MEM
  rw [List.mem_mergeSort] at MEM
  unfold pending_jobs at MEM
  rw [List.mem_filter] at MEM
  obtain ⟨_, PEND⟩ := MEM
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    not_le] at PEND
  exact PEND.1

theorem scheduler_sequential_jobs :
    sequential_jobs
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) := by
  intro j t cpu1 cpu2 SCHED1 SCHED2
  set l := sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
    (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t
  have MAP1 : scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority cpu1 t =
    nth_or_none l cpu1 :=
    scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
      H_priority_transitive H_priority_total t cpu1
  have MAP2 : scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority cpu2 t =
    nth_or_none l cpu2 :=
    scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
      H_priority_transitive H_priority_total t cpu2
  rw [SCHED1] at MAP1; rw [SCHED2] at MAP2
  have NODUP : l.Nodup := by
    show (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t).Nodup
    unfold sorted_pending_jobs pending_jobs
    rw [List.Perm.nodup_iff (List.mergeSort_perm _ _)]
    exact List.Nodup.filter _
      (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
        H_arrival_sequence_is_a_set 0 (t + 1))
  exact Fin.ext (nth_or_none_uniq l cpu1.val cpu2.val j NODUP MAP1.symm MAP2.symm)

theorem scheduler_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) := by
  intro j t
  induction t with
  | zero =>
    unfold service; simp
  | succ t IHt =>
    unfold service
    rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
    by_cases hlt : ∑ t_0 ∈ Finset.Ico 0 t, service_at (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j t_0 < job_cost j
    · have hseq := scheduler_sequential_jobs job_arrival job_cost num_cpus H_at_least_one_cpu
        arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
        H_priority_transitive H_priority_total
      have hle1 := service_at_most_one (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j hseq t
      omega
    · push_neg at hlt
      have heq : ∑ t_0 ∈ Finset.Ico 0 t, service_at (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j t_0 = job_cost j := by
        unfold service at IHt
        exact Nat.le_antisymm IHt hlt
      have hcomp : completed job_cost (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j t := by
        unfold completed service; omega
      have hnsched : ¬ scheduled (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j t := by
        intro ⟨cpu, hon⟩
        unfold scheduled_on at hon
        have hsched_eq := eq_of_beq hon
        rw [scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
          H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
          H_priority_transitive H_priority_total t cpu] at hsched_eq
        have hmem := nth_or_none_mem _ _ _ hsched_eq
        unfold sorted_pending_jobs at hmem
        rw [List.mem_mergeSort] at hmem
        unfold pending_jobs at hmem
        rw [List.mem_filter] at hmem
        obtain ⟨_, hpend⟩ := hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not, not_le] at hpend
        unfold completed at hcomp
        exact absurd hcomp (not_le.mpr hpend.2)
      have hzero := (not_scheduled_no_service (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) j t).mp hnsched
      omega

theorem scheduler_work_conserving :
    work_conserving job_arrival job_cost arr_seq
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) := by
  intro j t ARRj BACK cpu
  cases h_eq : scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority cpu t with
  | some j0 => exact ⟨j0, by unfold scheduled_on; rw [h_eq]; exact beq_self_eq_true _⟩
  | none =>
    exfalso
    have ⟨cpu_out, NTH, GE⟩ := scheduler_nth_or_none_backlogged job_arrival job_cost num_cpus
      H_at_least_one_cpu arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
      higher_eq_priority H_priority_transitive H_priority_total j t ARRj BACK
    rw [scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
      H_priority_transitive H_priority_total t cpu] at h_eq
    have hsize_none := (nth_or_none_size_none (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) cpu).mp h_eq
    have hsize_some := nth_or_none_size_some (sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t) cpu_out j NTH
    omega

theorem scheduler_respects_policy :
    respects_JLDP_policy job_arrival job_cost arr_seq
      (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) higher_eq_priority := by
  intro j j_hp t ARRj BACK ⟨cpu, SCHED⟩
  set sorted_jobs := sorted_pending_jobs job_arrival job_cost arr_seq higher_eq_priority
    (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t
  have ⟨cpu_out, SOME, GE⟩ := scheduler_nth_or_none_backlogged job_arrival job_cost num_cpus
    H_at_least_one_cpu arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    higher_eq_priority H_priority_transitive H_priority_total j t ARRj BACK
  unfold scheduled_on at SCHED
  have hsched_eq := eq_of_beq SCHED
  rw [scheduler_nth_or_none_mapping job_arrival job_cost num_cpus H_at_least_one_cpu arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    H_priority_transitive H_priority_total t cpu] at hsched_eq
  have hsize_some := nth_or_none_size_some sorted_jobs cpu_out j SOME
  have hlt : (cpu : ℕ) < cpu_out := Nat.lt_of_lt_of_le cpu.isLt GE
  have SORT : List.IsChain (fun a b => higher_eq_priority t a b = true) sorted_jobs := by
    show List.IsChain (fun a b => higher_eq_priority t a b = true)
      ((pending_jobs job_arrival job_cost arr_seq
        (scheduler job_arrival job_cost num_cpus arr_seq higher_eq_priority) t).mergeSort (higher_eq_priority t))
    have h_total : ∀ a b, (higher_eq_priority t a b || higher_eq_priority t b a) = true := by
      intro a b
      simp only [Bool.or_eq_true]
      exact H_priority_total t a b
    exact List.Pairwise.isChain
      (List.pairwise_mergeSort (fun a b c h1 h2 => H_priority_transitive t b a c h1 h2)
        h_total _)
  have EQ1 := nth_or_none_nth sorted_jobs (cpu : ℕ) j_hp j_hp hsched_eq
  have EQ2 := nth_or_none_nth sorted_jobs cpu_out j j_hp SOME
  rw [← EQ1, ← EQ2]
  exact sorted_lt_idx_implies_rel (higher_eq_priority t) sorted_jobs j_hp (cpu : ℕ) cpu_out
    (fun y x z => H_priority_transitive t y x z) SORT hlt hsize_some

end Proofs

end ConcreteScheduler

end Prosa.Classic.Implementation.Global.Basic.Schedule
