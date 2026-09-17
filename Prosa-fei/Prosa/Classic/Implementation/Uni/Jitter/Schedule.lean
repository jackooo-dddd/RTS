-- Translated from: ../rt-proofs/classic/implementation/uni/jitter/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

namespace Prosa.Classic.Implementation.Uni.Jitter.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Priority
open Prosa.Classic.Util.Minmax

namespace ConcreteScheduler

section Implementation

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (higher_eq_priority : JLDP_policy Job)

section ScheduleConstruction_

variable (sched_prefix : schedule Job)
variable (t : Time)

noncomputable def pending_jobs : List Job :=
  (actual_arrivals_up_to job_arrival job_jitter arr_seq t).filter
    (fun j => decide (actual_arrival job_arrival job_jitter j ≤ t) &&
              decide (¬ job_cost j ≤ service sched_prefix j t))

noncomputable def highest_priority_job : Option Job :=
  seq_min (higher_eq_priority t)
    (pending_jobs job_arrival job_cost job_jitter arr_seq sched_prefix t)

end ScheduleConstruction_

noncomputable def scheduler : schedule Job :=
  build_schedule_from_prefixes
    (fun sched t => highest_priority_job job_arrival job_cost job_jitter arr_seq
      higher_eq_priority sched t)
    (fun _ => none)

theorem scheduler_depends_only_on_prefix :
    ∀ (sched1 sched2 : schedule Job) (t : Time),
      (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      highest_priority_job job_arrival job_cost job_jitter arr_seq
        higher_eq_priority sched1 t =
      highest_priority_job job_arrival job_cost job_jitter arr_seq
        higher_eq_priority sched2 t := by
  intro sched1 sched2 t ALL
  unfold highest_priority_job
  suffices SAME : pending_jobs job_arrival job_cost job_jitter arr_seq sched1 t =
      pending_jobs job_arrival job_cost job_jitter arr_seq sched2 t by rw [SAME]
  unfold pending_jobs
  apply List.filter_congr
  intro j _
  have SERV : service sched1 j t = service sched2 j t := by
    unfold service service_during; apply Finset.sum_congr rfl; intro i hi;
    rw [Finset.mem_Ico] at hi; unfold service_at scheduled_at; rw [ALL i hi.2]
  rw [SERV]

theorem scheduler_uses_construction_function :
    ∀ t, scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority t =
      highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority
        (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) t := by
  intro t
  exact prefix_dependent_schedule_construction
    (fun sched t => highest_priority_job job_arrival job_cost job_jitter arr_seq
      higher_eq_priority sched t)
    (fun _ => none)
    (scheduler_depends_only_on_prefix job_arrival job_cost job_jitter arr_seq higher_eq_priority)
    t

end Implementation

#print axioms ConcreteScheduler.scheduler_depends_only_on_prefix
#print axioms ConcreteScheduler.scheduler_uses_construction_function

section Proofs

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
variable (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority)

include H_arrival_times_are_consistent H_no_duplicate_arrivals
        H_priority_is_reflexive H_priority_is_transitive H_priority_is_total

theorem scheduler_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) arr_seq := by
  intro j t SCHED
  have SCHED2 := SCHED
  rw [scheduled_at, scheduler_uses_construction_function] at SCHED2
  have IN := seq_min_in_seq (higher_eq_priority t)
    (pending_jobs job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) t)
    j (by rwa [beq_iff_eq] at SCHED2)
  simp only [pending_jobs, List.mem_filter] at IN
  exact in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq
    H_arrival_times_are_consistent j 0 (t + 1) IN.1

theorem scheduler_jobs_execute_after_jitter :
    jobs_execute_after_jitter job_arrival job_jitter
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) := by
  intro j t SCHED
  have SCHED2 := SCHED
  rw [scheduled_at, scheduler_uses_construction_function] at SCHED2
  have IN := seq_min_in_seq (higher_eq_priority t)
    (pending_jobs job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) t)
    j (by rwa [beq_iff_eq] at SCHED2)
  simp only [pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at IN
  exact IN.2.1

theorem scheduler_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) := by
  set sched := scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority with sched_def
  intro j t
  induction t with
  | zero =>
    simp [service, service_during]
  | succ n IHn =>
    -- service sched j (n+1) = service sched j n + service_at sched j n
    have hstep : service sched j (n + 1) = service sched j n + service_at sched j n := by
      unfold service service_during
      rw [show Finset.Ico 0 (n + 1) = Finset.Ico 0 n ∪ Finset.Ico n (n + 1) from
        (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le n) (Nat.le_succ n)).symm,
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 n (n + 1))]
      simp
    -- Case analysis: is service sched j n < job_cost j or service sched j n = job_cost j?
    by_cases hlt : service sched j n < job_cost j
    · -- service n < job_cost, so service (n+1) ≤ service n + 1 ≤ job_cost
      rw [hstep]
      have : service_at sched j n ≤ 1 := service_at_most_one sched j n
      omega
    · -- service n ≥ job_cost, but IHn says service n ≤ job_cost, so service n = job_cost
      push_neg at hlt
      have EQ : service sched j n = job_cost j := Nat.le_antisymm IHn hlt
      -- j is not scheduled at time n because it's completed
      rw [hstep]
      have hsa : service_at sched j n = 0 := by
        simp only [service_at, scheduled_at]
        cases hd : (sched n == some j) with
        | true =>
          exfalso
          -- sched n = highest_priority_job ... sched n by the construction
          have SCHED_EQ : sched n = highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority sched n := by
            rw [sched_def]; exact scheduler_uses_construction_function job_arrival job_cost job_jitter arr_seq higher_eq_priority n
          have hd2 : sched n = some j := by rwa [beq_iff_eq] at hd
          rw [SCHED_EQ] at hd2
          have IN := seq_min_in_seq (higher_eq_priority n)
            (pending_jobs job_arrival job_cost job_jitter arr_seq sched n)
            j hd2
          simp only [pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at IN
          exact IN.2.2 (show job_cost j ≤ service sched j n by omega)
        | false => simp [Bool.toNat]
      omega

def work_conserving_jitter
    (job_arrival : Job → Time) (job_cost : Job → Time) (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
      job_arrival job_cost job_jitter sched j t →
    ∃ j_other, scheduled_at sched j_other t = true

theorem scheduler_work_conserving :
    work_conserving_jitter job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority) := by
  set sched := scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority with sched_def
  intro j t IN BACK
  unfold Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged at BACK
  unfold Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending at BACK
  obtain ⟨⟨ARR, NOTCOMP⟩, NOTSCHED⟩ := BACK
  -- sched t = highest_priority_job ... sched t
  have SCHED_EQ : sched t = highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority sched t := by
    rw [sched_def]; exact scheduler_uses_construction_function job_arrival job_cost job_jitter arr_seq higher_eq_priority t
  -- If there's a highest priority job, we're done
  cases HP : highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority sched t with
  | some j_hp =>
    exact ⟨j_hp, by simp [scheduled_at]; rw [SCHED_EQ, HP]⟩
  | none =>
    -- If no highest priority job, then pending_jobs is empty
    -- But j should be in pending_jobs since j is backlogged
    exfalso
    have hj_in : j ∈ pending_jobs job_arrival job_cost job_jitter arr_seq sched t := by
      simp only [pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
          H_arrival_times_are_consistent j 0 (t + 1) IN
          ⟨Nat.zero_le _, by unfold jitter_has_passed at ARR; simp only [Time] at *; omega⟩
      · exact ⟨ARR, NOTCOMP⟩
    have := seq_min_exists (higher_eq_priority t)
      (pending_jobs job_arrival job_cost job_jitter arr_seq sched t) j hj_in
    unfold highest_priority_job at HP
    exact this HP

def respects_JLDP_policy_jitter
    (job_arrival : Job → Time) (job_cost : Job → Time) (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
      job_arrival job_cost job_jitter sched j t →
    scheduled_at sched j_hp t = true →
    priority t j_hp j = true

theorem scheduler_respects_policy :
    respects_JLDP_policy_jitter job_arrival job_cost job_jitter arr_seq
      (scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority)
      higher_eq_priority := by
  set sched := scheduler job_arrival job_cost job_jitter arr_seq higher_eq_priority with sched_def
  intro j j_hp t ARR1 BACK SCHED
  unfold Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged at BACK
  unfold Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending at BACK
  obtain ⟨⟨ARR, NOTCOMP⟩, NOTSCHED⟩ := BACK
  -- Rewrite scheduled_at using the construction function
  rw [scheduled_at, sched_def, scheduler_uses_construction_function] at SCHED
  have SCHED_eq : highest_priority_job job_arrival job_cost job_jitter arr_seq higher_eq_priority sched t = some j_hp := by
    rwa [beq_iff_eq] at SCHED
  -- j is in pending_jobs
  have IN : j ∈ pending_jobs job_arrival job_cost job_jitter arr_seq sched t := by
    simp only [pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
        H_arrival_times_are_consistent j 0 (t + 1) ARR1
        ⟨Nat.zero_le _, by unfold jitter_has_passed at ARR; simp only [Time] at *; omega⟩
    · exact ⟨ARR, NOTCOMP⟩
  -- seq_min computes min, so higher_eq_priority t j_hp j = true
  unfold highest_priority_job at SCHED_eq
  exact seq_min_computes_min (higher_eq_priority t)
    (fun x y z h1 h2 => H_priority_is_transitive t y x z h1 h2)
    (pending_jobs job_arrival job_cost job_jitter arr_seq sched t)
    (fun x y hx hy => by
      simp only [pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx hy
      exact H_priority_is_total x y t
        (in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq
          H_arrival_times_are_consistent x 0 (t + 1) hx.1)
        (in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq
          H_arrival_times_are_consistent y 0 (t + 1) hy.1))
    j_hp j SCHED_eq IN

end Proofs

end ConcreteScheduler

end Prosa.Classic.Implementation.Uni.Jitter.Schedule
