-- Translated from: ../rt-proofs/classic/model/schedule/uni/schedule.v
import Prosa.Classic.Util.Sum
import Prosa.Classic.Util.Step_function
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Util.Step_function.StepFunction
open Prosa.Classic.Util.Sum

section ScheduleDef
variable (Job : Type _) [DecidableEq Job]
def schedule := Time → Option Job
end ScheduleDef

section ScheduleProperties
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (sched : schedule Job)
section JobProperties
variable (j : Job)
def scheduled_at (t : Time) : Bool := sched t == some j
def service_at (t : Time) : Nat := (scheduled_at sched j t).toNat
def service_during (t1 t2 : Time) : Nat := ∑ t ∈ Finset.Ico t1 t2, service_at sched j t
def service (t : Time) : Nat := service_during sched j 0 t
def completed_by (t : Time) : Prop := job_cost j ≤ service sched j t
def pending (t : Time) : Prop := has_arrived job_arrival j t ∧ ¬ completed_by job_cost sched j t
def pending_earlier_and_at (t : Time) : Prop := arrived_before job_arrival j t ∧ ¬ completed_by job_cost sched j t
def backlogged (t : Time) : Prop := pending job_arrival job_cost sched j t ∧ ¬ (scheduled_at sched j t = true)
end JobProperties
section ProcessorProperties
def is_idle (t : Time) : Bool := sched t == none
def total_service_during (t1 t2 : Time) : Nat := ∑ t ∈ Finset.Ico t1 t2, (!(is_idle sched t)).toNat
def total_service (t2 : Time) : Nat := total_service_during sched 0 t2
end ProcessorProperties
section PropertyOfSequentiality
variable {Task : Type _} [DecidableEq Task]
variable (job_task : Job → Task)
def sequential_jobs : Prop :=
  ∀ j1 j2 t, job_task j1 = job_task j2 → job_arrival j1 < job_arrival j2 → scheduled_at sched j2 t = true → completed_by job_cost sched j1 t
theorem scheduler_executes_job_with_earliest_arrival
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (j1 j2 : Job) (t : Time) (h_same_task : job_task j1 = job_task j2)
    (h_not_completed : ¬ completed_by job_cost sched j2 t) (h_sched : scheduled_at sched j1 t = true) :
    job_arrival j1 ≤ job_arrival j2 := by
  by_contra h; push_neg at h; apply h_not_completed
  exact H_sequential_jobs j2 j1 t h_same_task.symm h h_sched
end PropertyOfSequentiality
end ScheduleProperties

section ValidSchedules
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (sched : schedule Job)
def jobs_come_from_arrival_sequence (arr_seq : arrival_sequence Job) : Prop := ∀ j t, scheduled_at sched j t = true → arrives_in arr_seq j
def jobs_must_arrive_to_execute : Prop := ∀ j t, scheduled_at sched j t = true → has_arrived job_arrival j t
def completed_jobs_dont_execute : Prop := ∀ j t, service sched j t ≤ job_cost j
end ValidSchedules

section Lemmas
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (sched : schedule Job)
def remaining_cost (j : Job) (t : Time) : Nat := job_cost j - service sched j t
section Service
variable (j : Job)
theorem service_at_most_one : ∀ t, service_at sched j t ≤ 1 := by
  intro t; simp only [service_at, scheduled_at]; cases h : (sched t == some j) <;> simp [Bool.toNat]
theorem cumulative_service_le_delta : ∀ t delta, service_during sched j t (t + delta) ≤ delta := by
  intro t delta; simp only [service_during]
  calc ∑ t_1 ∈ Finset.Ico t (t + delta), service_at sched j t_1
      ≤ ∑ _t_1 ∈ Finset.Ico t (t + delta), 1 := by
        apply Finset.sum_le_sum; intros i _; exact service_at_most_one sched j i
    _ = delta := by rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]; simp only [Time] at *; omega
variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
include H_completed_jobs
theorem scheduled_implies_positive_remaining_cost :
    ∀ t, scheduled_at sched j t = true → remaining_cost job_cost sched j t > 0 := by
  intro t hsched
  unfold remaining_cost
  suffices h : service sched j t < job_cost j by omega
  have h_sa : service_at sched j t = 1 := by
    simp only [service_at, scheduled_at] at hsched ⊢; simp [hsched, Bool.toNat]
  have h_comp := H_completed_jobs j (t + 1)
  have h_le : service sched j t + service_at sched j t ≤ service sched j (t + 1) := by
    show service_during sched j 0 t + service_at sched j t ≤ service_during sched j 0 (t + 1)
    simp only [service_during]
    rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
  omega
end Service

section Completion
variable (j : Job)
theorem completion_monotonic : ∀ t t', t ≤ t' → completed_by job_cost sched j t → completed_by job_cost sched j t' := by
  intro t t' hle hcomp; simp only [completed_by, service, service_during] at *
  calc job_cost j ≤ ∑ t_1 ∈ Finset.Ico 0 t, service_at sched j t_1 := hcomp
    _ ≤ ∑ t_1 ∈ Finset.Ico 0 t', service_at sched j t_1 := by
        apply Finset.sum_le_sum_of_subset; intro x hx; rw [Finset.mem_Ico] at hx ⊢; exact ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩
variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
include H_completed_jobs
theorem completed_implies_not_scheduled : ∀ t, completed_by job_cost sched j t → ¬ (scheduled_at sched j t = true) := by
  intro t hcomp hsched
  have h_sa : service_at sched j t = 1 := by
    simp only [service_at, scheduled_at] at hsched ⊢; simp [hsched, Bool.toNat]
  have h_bound := H_completed_jobs j (t + 1)
  unfold completed_by at hcomp
  -- service(t+1) ≥ service(t) + service_at(t) = service(t) + 1 ≥ job_cost j + 1
  -- But h_bound: service(t+1) ≤ job_cost j
  -- Contradiction
  apply Nat.not_lt.mpr h_bound
  calc job_cost j
      ≤ service sched j t := hcomp
    _ < service sched j t + 1 := Nat.lt_succ_of_le (le_refl _)
    _ = service sched j t + service_at sched j t := by omega
    _ ≤ service sched j (t + 1) := by
        show service_during sched j 0 t + service_at sched j t ≤ service_during sched j 0 (t + 1)
        simp only [service_during]
        rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
theorem scheduled_implies_not_completed : ∀ t, scheduled_at sched j t = true → ¬ completed_by job_cost sched j t := by
  intro t hsched hcomp; exact completed_implies_not_scheduled job_cost sched j H_completed_jobs t hcomp hsched
theorem cumulative_service_le_job_cost : ∀ t t', service_during sched j t t' ≤ job_cost j := by
  intro t t'; by_cases h : t ≤ t'
  · simp only [service_during]
    calc ∑ t_1 ∈ Finset.Ico t t', service_at sched j t_1
        ≤ ∑ t_1 ∈ Finset.Ico 0 t', service_at sched j t_1 := by
          apply Finset.sum_le_sum_of_subset; intro x hx; rw [Finset.mem_Ico] at hx ⊢; exact ⟨Nat.zero_le _, hx.2⟩
      _ ≤ job_cost j := H_completed_jobs j t'
  · push_neg at h; simp only [service_during]; rw [Finset.Ico_eq_empty (by simp only [Time] at *; omega)]; simp
theorem job_doesnt_complete_before_remaining_cost :
    ∀ t, ¬ completed_by job_cost sched j t → ¬ completed_by job_cost sched j (t + remaining_cost job_cost sched j t - 1) := by
  intro t hnotcomp
  have hlt : service sched j t < job_cost j := by
    by_contra h; push_neg at h; exact hnotcomp (show completed_by job_cost sched j t from h)
  have hle_s : service sched j t ≤ job_cost j := Nat.le_of_lt hlt
  have hdelta_pos : 0 < job_cost j - service sched j t := Nat.sub_pos_of_lt hlt
  -- Key: t < t + delta, so t ≤ t + delta - 1
  have hlt_t : t < t + (job_cost j - service sched j t) := Nat.lt_add_of_pos_right hdelta_pos
  have hle_t : t ≤ t + (job_cost j - service sched j t) - 1 := Nat.le_sub_one_of_lt hlt_t
  -- Key: t + delta - 1 = t + (delta - 1) when delta > 0
  have heq_time : t + (job_cost j - service sched j t) - 1 = t + (job_cost j - service sched j t - 1) :=
    Nat.add_sub_assoc hdelta_pos t
  intro hcomp
  have hcomp' : job_cost j ≤ service sched j (t + remaining_cost job_cost sched j t - 1) := hcomp
  -- Split service at (t + rc - 1) into service at t plus service_during
  have h_split : service sched j (t + remaining_cost job_cost sched j t - 1) =
      service sched j t + service_during sched j t (t + remaining_cost job_cost sched j t - 1) := by
    show service_during sched j 0 (t + remaining_cost job_cost sched j t - 1) =
      service_during sched j 0 t + service_during sched j t (t + remaining_cost job_cost sched j t - 1)
    simp only [service_during]
    rw [show t + remaining_cost job_cost sched j t - 1 = t + (job_cost j - service sched j t) - 1 from rfl]
    rw [(Finset.Ico_union_Ico_eq_Ico (Nat.zero_le t) hle_t).symm,
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 t
          (t + (job_cost j - service sched j t) - 1))]
  -- Bound: service_during ≤ delta - 1
  have hbound : service_during sched j t (t + remaining_cost job_cost sched j t - 1) ≤
      job_cost j - service sched j t - 1 := by
    show service_during sched j t (t + (job_cost j - service sched j t) - 1) ≤
      job_cost j - service sched j t - 1
    rw [heq_time]
    exact cumulative_service_le_delta sched j t (job_cost j - service sched j t - 1)
  rw [h_split] at hcomp'
  -- Now: job_cost j ≤ service j t + sd, where sd ≤ job_cost j - service j t - 1
  -- So: job_cost j ≤ service j t + (job_cost j - service j t - 1) = job_cost j - 1 < job_cost j
  -- Use: a + (b - a - 1) < b when a < b
  have key : service sched j t + (job_cost j - service sched j t - 1) < job_cost j := by
    have h1 : job_cost j - service sched j t - 1 < job_cost j - service sched j t := Nat.sub_lt hdelta_pos Nat.one_pos
    calc service sched j t + (job_cost j - service sched j t - 1)
        < service sched j t + (job_cost j - service sched j t) := Nat.add_lt_add_left h1 _
      _ = job_cost j := Nat.add_sub_cancel' hle_s
  exact absurd (le_trans hcomp' (Nat.add_le_add_left hbound _)) (Nat.not_le.mpr key)
section JobMustBeScheduled
variable (H_positive_cost : job_cost j > 0)
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
include H_positive_cost H_jobs_must_arrive
theorem completed_implies_scheduled_before :
    ∀ t, completed_by job_cost sched j t → ∃ t', job_arrival j ≤ t' ∧ t' < t ∧ scheduled_at sched j t' = true := by
  intro t; induction t with
  | zero =>
    intro hcomp; exfalso
    simp only [completed_by, service, service_during] at hcomp
    rw [Finset.Ico_self] at hcomp; simp at hcomp; simp only [Time] at *; omega
  | succ n ih =>
    intro hcomp
    by_cases h : completed_by job_cost sched j n
    · obtain ⟨t', ht1, ht2, ht3⟩ := ih h
      exact ⟨t', ht1, by simp only [Time] at *; omega, ht3⟩
    · -- Not completed at n, but completed at n+1
      -- So service_at n must be 1, meaning j is scheduled at n
      have hsched : scheduled_at sched j n = true := by
        by_contra hns
        simp only [completed_by, service, service_during] at hcomp h
        push_neg at h
        rw [Finset.sum_Ico_succ_top (Nat.zero_le n)] at hcomp
        have hsa : service_at sched j n = 0 := by
          simp only [service_at, scheduled_at] at hns ⊢
          cases hd : (sched n == some j) <;> simp [Bool.toNat]
          · exact absurd hd hns
        simp only [Time] at *; omega
      exact ⟨n, H_jobs_must_arrive j n hsched, Nat.lt_succ_of_le (le_refl n), hsched⟩
end JobMustBeScheduled
end Completion

section Arrival
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
include H_jobs_must_arrive
variable (j : Job)
theorem service_before_job_arrival_zero : ∀ t, t < job_arrival j → service_at sched j t = 0 := by
  intro t ht; simp only [service_at, scheduled_at]
  cases hd : (sched t == some j)
  · simp [Bool.toNat]
  · exfalso; have heq : sched t = some j := by rwa [beq_iff_eq] at hd
    have hsched : scheduled_at sched j t = true := by simp [scheduled_at, heq]
    have harr := H_jobs_must_arrive j t hsched; unfold has_arrived at harr; simp only [Time] at *; omega
theorem cumulative_service_before_job_arrival_zero :
    ∀ t1 t2, t2 ≤ job_arrival j → ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
  intro t1 t2 hle; apply Finset.sum_eq_zero; intro i hi; rw [Finset.mem_Ico] at hi
  exact service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive j i (by simp only [Time] at *; omega)
theorem ignore_service_before_arrival :
    ∀ t1 t2, t1 ≤ job_arrival j → t2 ≥ job_arrival j →
      ∑ t ∈ Finset.Ico t1 t2, service_at sched j t = ∑ t ∈ Finset.Ico (job_arrival j) t2, service_at sched j t := by
  intro t1 t2 hle1 hge2
  rw [(Finset.Ico_union_Ico_eq_Ico hle1 hge2).symm, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive t1 (job_arrival j) t2),
      cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive j t1 (job_arrival j) (le_refl _)]; simp
end Arrival

section Pending
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
include H_jobs_must_arrive H_completed_jobs
variable (j : Job)
theorem scheduled_implies_pending : ∀ t, scheduled_at sched j t = true → pending job_arrival job_cost sched j t := by
  intro t hsched; exact ⟨H_jobs_must_arrive j t hsched, scheduled_implies_not_completed job_cost sched j H_completed_jobs t hsched⟩
variable (arr_seq : arrival_sequence Job)
theorem job_pending_at_arrival : arrives_in arr_seq j → job_cost j > 0 → pending job_arrival job_cost sched j (job_arrival j) := by
  intro _ hpos; constructor
  · simp [has_arrived]
  · intro hcomp; unfold completed_by service service_during at hcomp
    rw [ignore_service_before_arrival job_arrival sched H_jobs_must_arrive j 0 (job_arrival j) (Nat.zero_le _) (le_refl _)] at hcomp
    rw [Finset.Ico_self] at hcomp; simp at hcomp; simp only [Time] at *; omega
end Pending

section OnlyOneJobScheduled
variable (j1 j2 : Job)
theorem only_one_job_scheduled : ∀ t, scheduled_at sched j1 t = true → scheduled_at sched j2 t = true → j1 = j2 := by
  intro t h1 h2; simp [scheduled_at] at h1 h2; rw [h1] at h2; exact Option.some_injective _ h2
end OnlyOneJobScheduled

section ServiceIsAStepFunction
theorem service_is_a_step_function : ∀ j, is_step_function (service sched j) := by
  intro j t; simp only [service, service_during]
  rw [show (t + 1) = (t + 1) from rfl, Finset.sum_Ico_succ_top (Nat.zero_le (t))]
  exact Nat.add_le_add_left (service_at_most_one sched j t) _
variable (j : Job)
variable (t : Time)
variable (s0 : Time)
variable (H_less_than_s : s0 < service sched j t)
include H_less_than_s
theorem exists_intermediate_service : ∃ t0, t0 < t ∧ service sched j t0 = s0 := by
  obtain ⟨x_mid, _, hlt, heq⟩ := exists_intermediate_point (service sched j) (service_is_a_step_function sched j)
    0 t (Nat.zero_le t) s0 ⟨by simp [service, service_during], H_less_than_s⟩
  exact ⟨x_mid, hlt, heq⟩
end ServiceIsAStepFunction

section ScheduledAtEarlierTime
theorem scheduled_at_earlier_time : ∀ j t, service sched j t > 0 → ∃ t0, t0 < t ∧ scheduled_at sched j t0 = true := by
  intro j t hgt; unfold service service_during at hgt; by_contra h; push_neg at h
  have hzero : ∀ i ∈ Finset.Ico 0 t, service_at sched j i = 0 := by
    intro i hi; rw [Finset.mem_Ico] at hi; simp only [service_at, scheduled_at]
    cases hd : (sched i == some j)
    · simp [Bool.toNat]
    · exfalso; exact absurd (show scheduled_at sched j i = true by simp [scheduled_at, beq_iff_eq.mp hd]) (h i hi.2)
  rw [Finset.sum_eq_zero hzero] at hgt; simp only [Time] at *; omega
end ScheduledAtEarlierTime

section ServiceNotZero
variable (j : Job) (t1 t2 : Time)
variable (H_service_not_zero : service_during sched j t1 t2 > 0)
include H_service_not_zero
theorem cumulative_service_implies_scheduled : ∃ t, t1 ≤ t ∧ t < t2 ∧ scheduled_at sched j t = true := by
  by_contra h; push_neg at h
  have hzero : ∀ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
    intro i hi; rw [Finset.mem_Ico] at hi; simp only [service_at, scheduled_at]
    cases hd : (sched i == some j)
    · simp [Bool.toNat]
    · exfalso; exact (h i hi.1 hi.2) (show scheduled_at sched j i = true by simp [scheduled_at, beq_iff_eq.mp hd])
  simp only [service_during] at H_service_not_zero; rw [Finset.sum_eq_zero hzero] at H_service_not_zero; simp only [Time] at *; omega
end ServiceNotZero

section TimesWithSameService
variable (j : Job) (t1 t2 : Time)
variable (H_same_service : service sched j t1 = service sched j t2)
include H_same_service
theorem same_service_implies_scheduled_at_earlier_times :
    (∃ t : Fin t1, scheduled_at sched j t = true) ↔ (∃ t' : Fin t2, scheduled_at sched j t' = true) := by
  constructor
  · rintro ⟨⟨t0, ht0⟩, hsched⟩
    by_cases h12 : t1 ≤ t2
    · exact ⟨⟨t0, lt_of_lt_of_le ht0 h12⟩, hsched⟩
    · push_neg at h12; by_cases ht0t2 : t0 < t2
      · exact ⟨⟨t0, ht0t2⟩, hsched⟩
      · push_neg at ht0t2; exfalso
        simp only [service, service_during] at H_same_service
        rw [(Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt h12)).symm,
            Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)] at H_same_service
        have hsa : service_at sched j t0 = 1 := by simp only [service_at, scheduled_at] at hsched ⊢; simp [hsched, Bool.toNat]
        have hmem : t0 ∈ Finset.Ico t2 t1 := by rw [Finset.mem_Ico]; exact ⟨ht0t2, ht0⟩
        have := le_trans (show 1 ≤ service_at sched j t0 by simp only [Time] at *; omega) (Finset.single_le_sum (by intro i _; simp only [Time] at *; omega) hmem)
        simp only [Time] at *; omega
  · rintro ⟨⟨t0, ht0⟩, hsched⟩
    by_cases h21 : t2 ≤ t1
    · exact ⟨⟨t0, lt_of_lt_of_le ht0 h21⟩, hsched⟩
    · push_neg at h21; by_cases ht0t1 : t0 < t1
      · exact ⟨⟨t0, ht0t1⟩, hsched⟩
      · push_neg at ht0t1; exfalso
        simp only [service, service_during] at H_same_service
        rw [(Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt h21)).symm,
            Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)] at H_same_service
        have hsa : service_at sched j t0 = 1 := by simp only [service_at, scheduled_at] at hsched ⊢; simp [hsched, Bool.toNat]
        have hmem : t0 ∈ Finset.Ico t1 t2 := by rw [Finset.mem_Ico]; exact ⟨ht0t1, ht0⟩
        have := le_trans (show 1 ≤ service_at sched j t0 by simp only [Time] at *; omega) (Finset.single_le_sum (by intro i _; simp only [Time] at *; omega) hmem)
        simp only [Time] at *; omega
end TimesWithSameService
end Lemmas
end Prosa.Classic.Model.Schedule.Uni.Schedule
