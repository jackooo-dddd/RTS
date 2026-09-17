-- Translated from: ../rt-proofs/classic/model/schedule/uni/nonpreemptive/schedule.v
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule

section Definitions

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (sched : schedule Job)

noncomputable def job_completed_by := completed_by job_cost sched
noncomputable def job_remaining_cost (j : Job) (t : Time) := remaining_cost job_cost sched j t

def is_nonpreemptive_schedule : Prop :=
  ∀ j t t',
    t ≤ t' →
    scheduled_at sched j t = true →
    ¬ completed_by job_cost sched j t' →
    scheduled_at sched j t' = true

section Lemmas

variable (H_nonpreemptive : is_nonpreemptive_schedule job_cost sched)

section BasicLemmas

variable (j : Job)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
include H_nonpreemptive H_completed_jobs_dont_execute

theorem continuity_of_nonpreemptive_scheduling :
    ∀ t t1 t2,
      t1 ≤ t ∧ t ≤ t2 →
      scheduled_at sched j t1 = true →
      scheduled_at sched j t2 = true →
      scheduled_at sched j t = true := by
  intro t t1 t2 ⟨hle1, hle2⟩ hsched1 hsched2
  apply H_nonpreemptive j t1 t hle1 hsched1
  intro hcomp
  have hcomp2 := completion_monotonic job_cost sched j t t2 hle2 hcomp
  exact scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t2 hsched2 hcomp2

theorem in_nonpreemption_schedule_preemption_implies_completeness :
    ∀ t t',
      t ≤ t' →
      scheduled_at sched j t = true →
      ¬ (scheduled_at sched j t' = true) →
      completed_by job_cost sched j t' := by
  intro t t' hle hsched hnsched
  by_contra hnotcomp
  exact hnsched (H_nonpreemptive j t t' hle hsched hnotcomp)

end BasicLemmas

section CompletionUnderNonpreemptive

variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
include H_nonpreemptive H_completed_jobs_dont_execute

theorem job_completes_after_remaining_cost :
    ∀ j t,
      scheduled_at sched j t = true →
      completed_by job_cost sched j (t + remaining_cost job_cost sched j t) := by
  intro j t hsched
  unfold completed_by
  have hle : service sched j t ≤ job_cost j := H_completed_jobs_dont_execute j t
  have hsched_all : ∀ i, t ≤ i → i < t + remaining_cost job_cost sched j t →
      scheduled_at sched j i = true := by
    intro i hti hilt
    apply H_nonpreemptive j t i hti hsched
    intro hcomp_i
    have hnotcomp_t : ¬ completed_by job_cost sched j t :=
      scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t hsched
    have hnotcomp_rem : ¬ completed_by job_cost sched j (t + remaining_cost job_cost sched j t - 1) :=
      job_doesnt_complete_before_remaining_cost job_cost sched j H_completed_jobs_dont_execute t hnotcomp_t
    apply hnotcomp_rem
    apply completion_monotonic job_cost sched j i (t + remaining_cost job_cost sched j t - 1)
      (by simp only [Time] at *; omega) hcomp_i
  have hserv_ge : remaining_cost job_cost sched j t ≤ service_during sched j t (t + remaining_cost job_cost sched j t) := by
    calc remaining_cost job_cost sched j t
        = ∑ _i ∈ Finset.Ico t (t + remaining_cost job_cost sched j t), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]; simp only [Time] at *; omega
      _ ≤ ∑ i ∈ Finset.Ico t (t + remaining_cost job_cost sched j t), service_at sched j i := by
          apply Finset.sum_le_sum; intro i hi; rw [Finset.mem_Ico] at hi
          have := hsched_all i hi.1 hi.2
          simp only [service_at]; rw [this]; simp [Bool.toNat]
  have hsplit : service sched j (t + remaining_cost job_cost sched j t) =
      service sched j t + service_during sched j t (t + remaining_cost job_cost sched j t) := by
    unfold service service_during
    rw [show Finset.Ico 0 (t + remaining_cost job_cost sched j t) =
          Finset.Ico 0 t ∪ Finset.Ico t (t + remaining_cost job_cost sched j t) from by
      rw [Finset.Ico_union_Ico_eq_Ico (Nat.zero_le t) (Nat.le_add_right t _)],
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 t (t + remaining_cost job_cost sched j t))]
  -- The goal is: job_cost j ≤ service sched j (t + remaining_cost ...)
  -- hsplit: service ... = service ... + service_during ...
  -- hserv_ge: remaining_cost ... ≤ service_during ...
  -- hle: service sched j t ≤ job_cost j
  show job_cost j ≤ service sched j (t + remaining_cost job_cost sched j t)
  rw [hsplit]
  -- Now goal: job_cost j ≤ service sched j t + service_during sched j t (t + remaining_cost ...)
  exact le_trans (show job_cost j ≤ service sched j t + remaining_cost job_cost sched j t from
    (Nat.add_sub_cancel' hle).symm ▸ le_refl _)
    (Nat.add_le_add_left hserv_ge _)

end CompletionUnderNonpreemptive

section ExecutionInterval

variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
variable (j : Job)
variable (t : Time)
variable (H_j_is_scheduled_at_t : scheduled_at sched j t = true)
include H_nonpreemptive H_completed_jobs_dont_execute H_j_is_scheduled_at_t

section LeftBound

theorem j_is_scheduled_at_t_minus_service :
    scheduled_at sched j (t - service sched j t) = true := by
  by_contra hcontra
  -- If service j t = 0, then t - 0 = t, contradiction since j IS scheduled at t
  by_cases hserv0 : service sched j t = 0
  · simp only [hserv0, Nat.sub_zero] at hcontra; exact hcontra H_j_is_scheduled_at_t
  -- service j t > 0 and service j t ≤ t
  have hserv_pos : service sched j t > 0 := Nat.pos_of_ne_zero hserv0
  have hserv_le_t : service sched j t ≤ t := by
    have := cumulative_service_le_delta sched j 0 t
    simp only [service, service_during, Nat.zero_add] at this ⊢; exact this
  -- No time point i ≤ t - service j t has j scheduled (by continuity with t)
  have hnotbefore : ∀ i, i ≤ t - service sched j t → ¬ (scheduled_at sched j i = true) := by
    intro i hi hsched_i
    exact hcontra (continuity_of_nonpreemptive_scheduling job_cost sched H_nonpreemptive j
      H_completed_jobs_dont_execute (t - service sched j t) i t
      ⟨hi, Nat.sub_le t _⟩ hsched_i H_j_is_scheduled_at_t)
  -- All service_at in [0, t-s+1) are 0
  have hleft_zero : ∀ i, i ∈ Finset.Ico 0 (t - service sched j t + 1) → service_at sched j i = 0 := by
    intro i hi; rw [Finset.mem_Ico] at hi
    simp only [service_at]
    cases h : scheduled_at sched j i
    · simp [Bool.toNat]
    · exfalso; exact hnotbefore i (by simp only [Time] at *; omega) h
  -- sum over [t-s+1, t) ≤ t - (t-s+1) = s - 1
  have hright_le : ∑ i ∈ Finset.Ico (t - service sched j t + 1) t, service_at sched j i ≤
      service sched j t - 1 := by
    calc ∑ i ∈ Finset.Ico (t - service sched j t + 1) t, service_at sched j i
        ≤ ∑ _i ∈ Finset.Ico (t - service sched j t + 1) t, 1 :=
          Finset.sum_le_sum (fun i _ => service_at_most_one sched j i)
      _ = t - (t - service sched j t + 1) := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
      _ = service sched j t - 1 := by simp only [Time] at *; omega
  -- Split: service j t = sum [0, t-s+1) + sum [t-s+1, t)
  have hsplit_serv : ∑ i ∈ Finset.Ico 0 t, service_at sched j i =
      ∑ i ∈ Finset.Ico 0 (t - service sched j t + 1), service_at sched j i +
      ∑ i ∈ Finset.Ico (t - service sched j t + 1) t, service_at sched j i := by
    rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 (t - service sched j t + 1) t),
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by simp only [Time] at *; omega)]
  rw [Finset.sum_eq_zero hleft_zero, Nat.zero_add] at hsplit_serv
  -- hsplit_serv: sum[0,t) = sum[t-s+1, t)
  -- hright_le: sum[t-s+1, t) ≤ service j t - 1
  -- service j t = sum[0,t) (by definition)
  -- So service j t ≤ service j t - 1, contradiction since service j t > 0
  have hserv_unfold : service sched j t = ∑ i ∈ Finset.Ico 0 t, service_at sched j i := rfl
  omega

theorem j_is_not_scheduled_at_t_minus_service_minus_one :
    t - service sched j t > 0 →
    ¬ (scheduled_at sched j (t - service sched j t - 1) = true) := by
  intro hgt hsched_contra
  -- L1: j doesn't complete before t + remaining_cost j t - 1
  have hnotcomp_t : ¬ completed_by job_cost sched j t :=
    scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t H_j_is_scheduled_at_t
  have L1 : ¬ completed_by job_cost sched j (t + remaining_cost job_cost sched j t - 1) :=
    job_doesnt_complete_before_remaining_cost job_cost sched j H_completed_jobs_dont_execute t hnotcomp_t
  -- L2: j completes at (t - service j t - 1) + remaining_cost j (t - service j t - 1)
  have L2 : completed_by job_cost sched j ((t - service sched j t - 1) + remaining_cost job_cost sched j (t - service sched j t - 1)) :=
    job_completes_after_remaining_cost job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j (t - service sched j t - 1) hsched_contra
  -- Key: service j (t - service j t - 1) = 0
  have hserv_zero : service sched j (t - service sched j t - 1) = 0 := by
    by_contra hne
    have hpos : service sched j (t - service sched j t - 1) > 0 := by omega
    obtain ⟨t', ht'lt, hsched_t'⟩ := scheduled_at_earlier_time sched j (t - service sched j t - 1) hpos
    have hcomp_t' := job_completes_after_remaining_cost job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t' hsched_t'
    have hle_rem : t' + remaining_cost job_cost sched j t' ≤ t + remaining_cost job_cost sched j t - 1 := by
      simp only [remaining_cost]
      have h1 := H_completed_jobs_dont_execute j t'
      have h2 := H_completed_jobs_dont_execute j t
      have h3 := cumulative_service_le_delta sched j 0 t'
      have h4 := cumulative_service_le_delta sched j 0 t
      simp only [service, service_during] at h3 h4
      simp only [Time] at *
      omega
    exact L1 (completion_monotonic job_cost sched j _ _ hle_rem hcomp_t')
  -- remaining_cost at (t - service j t - 1) = job_cost j
  have hrem_eq : remaining_cost job_cost sched j (t - service sched j t - 1) = job_cost j := by
    simp only [remaining_cost, hserv_zero, Nat.sub_zero]
  -- Target equality
  have htarget : (t - service sched j t - 1) + remaining_cost job_cost sched j (t - service sched j t - 1) = t + remaining_cost job_cost sched j t - 1 := by
    rw [hrem_eq]
    simp only [remaining_cost]
    have hle := H_completed_jobs_dont_execute j t
    have hserv_le := cumulative_service_le_delta sched j 0 t
    simp only [service, service_during] at hserv_le
    simp only [Time] at *
    omega
  rw [htarget] at L2
  exact L1 L2

theorem j_is_not_scheduled_earlier_t_minus_service :
    ∀ t',
      t' < t - service sched j t →
      ¬ (scheduled_at sched j t' = true) := by
  intro t' hlt hsched_t'
  have hgt : t - service sched j t > 0 := by simp only [Time] at *; omega
  have hnotsched := j_is_not_scheduled_at_t_minus_service_minus_one job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t H_j_is_scheduled_at_t hgt
  apply hnotsched
  apply continuity_of_nonpreemptive_scheduling job_cost sched H_nonpreemptive j H_completed_jobs_dont_execute (t - service sched j t - 1) t' t
  · constructor
    · simp only [Time] at *; omega
    · simp only [Time] at *; omega
  · exact hsched_t'
  · exact H_j_is_scheduled_at_t

end LeftBound

section RightBound

theorem j_is_scheduled_at_t_plus_remaining_cost_minus_one :
    scheduled_at sched j (t + remaining_cost job_cost sched j t - 1) = true := by
  by_contra hnsched
  have hnotcomp : ¬ completed_by job_cost sched j t :=
    scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t H_j_is_scheduled_at_t
  have hnotcomp' : ¬ completed_by job_cost sched j (t + remaining_cost job_cost sched j t - 1) :=
    job_doesnt_complete_before_remaining_cost job_cost sched j H_completed_jobs_dont_execute t hnotcomp
  have hle : t ≤ t + remaining_cost job_cost sched j t - 1 := by
    have hpos := scheduled_implies_positive_remaining_cost job_cost sched j H_completed_jobs_dont_execute t H_j_is_scheduled_at_t
    simp only [Time] at *; omega
  have hcomp := in_nonpreemption_schedule_preemption_implies_completeness job_cost sched H_nonpreemptive j H_completed_jobs_dont_execute t (t + remaining_cost job_cost sched j t - 1) hle H_j_is_scheduled_at_t hnsched
  exact hnotcomp' hcomp

theorem j_is_not_scheduled_after_t_plus_remaining_cost_minus_one :
    ∀ t',
      t + remaining_cost job_cost sched j t ≤ t' →
      ¬ (scheduled_at sched j t' = true) := by
  intro t' hle hsched
  have hcomp := job_completes_after_remaining_cost job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t H_j_is_scheduled_at_t
  have hcomp' := completion_monotonic job_cost sched j (t + remaining_cost job_cost sched j t) t' hle hcomp
  exact scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute t' hsched hcomp'

end RightBound

theorem nonpreemptive_executing_interval :
    ∀ t',
      t - service sched j t ≤ t' ∧ t' < t + remaining_cost job_cost sched j t →
      scheduled_at sched j t' = true := by
  intro t' ⟨hge, hlt⟩
  have hsched1 := j_is_scheduled_at_t_minus_service job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t H_j_is_scheduled_at_t
  have hsched2 := j_is_scheduled_at_t_plus_remaining_cost_minus_one job_cost sched H_nonpreemptive H_completed_jobs_dont_execute j t H_j_is_scheduled_at_t
  apply continuity_of_nonpreemptive_scheduling job_cost sched H_nonpreemptive j H_completed_jobs_dont_execute t' (t - service sched j t) (t + remaining_cost job_cost sched j t - 1)
  · exact ⟨hge, by simp only [Time] at *; omega⟩
  · exact hsched1
  · exact hsched2

end ExecutionInterval

end Lemmas

end Definitions

end Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
