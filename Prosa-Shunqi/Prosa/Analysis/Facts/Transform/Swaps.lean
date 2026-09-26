-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/transform/swaps.v

import Prosa.Analysis.Facts.Transform.ReplaceAt
import Prosa.Analysis.Facts.Behavior.Deadlines

namespace Prosa.Analysis.Facts.Transform.Swaps

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Facts.Transform.ReplaceAt
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Deadlines

/-! Invariants of schedules in which the allocations at two instants have been
swapped. Representation: a single comparison in `Prop` position is the Lean
proposition; `a != b` is `decide (a ≠ b) = true`; `~~ b` is `!b`; `P \/ Q` is
`P ∨ Q`; Boolean equalities are equalities of `Bool`; the section-local
`Let sched'` is inlined as `swapped sched t1 t2`. Binder orders follow the
elaborated types (unused section context and hypotheses are absent). -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

section SwappedFacts

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

/-- The swapped schedule is the original one read through the transposition of
`t1` and `t2`. -/
private theorem swapped_eq (sched : schedule PState) (t1 t2 : instant) (x : instant) :
    swapped sched t1 t2 x = sched (Equiv.swap t1 t2 x) := by
  unfold swapped replace_at
  by_cases h2 : x = t2
  · subst h2; simp
  · by_cases h1 : x = t1
    · subst h1
      have : (t2 == x) = false := by simp [Ne.symm h2]
      simp [this, Equiv.swap_apply_left]
    · have e2 : (t2 == x) = false := by simp [Ne.symm h2]
      have e1 : (t1 == x) = false := by simp [Ne.symm h1]
      simp [e1, e2, Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem service_swapped (sched : schedule PState) (t1 t2 : instant) (j : Job) (t : instant) :
    service (swapped sched t1 t2) j t =
      ∑ x ∈ Finset.Ico 0 t, service_at sched j (Equiv.swap t1 t2 x) := by
  unfold service service_during
  apply Finset.sum_congr rfl
  intro x _
  unfold service_at
  rw [swapped_eq]

/-- If `t1 = t2`, the swapped schedule is the original one. -/
theorem trivial_swap (sched : schedule PState) (t1 t2 : instant) :
    t1 = t2 → ∀ t : instant, sched t = swapped sched t1 t2 t := by
  intro h t
  subst h
  rw [swapped_eq, Equiv.swap_self, Equiv.refl_apply]

/-- If `t1 = t2`, the service is unchanged. -/
theorem trivial_swap_service_invariant (sched : schedule PState) (t1 t2 : instant) :
    t1 = t2 → ∀ (t : instant) (j : Job), service sched j t = service (swapped sched t1 t2) j t := by
  intro h t j
  unfold service service_during
  apply Finset.sum_congr rfl
  intro x _
  unfold service_at
  rw [← trivial_swap sched t1 t2 h x]

/-- Times other than `t1` and `t2` are unchanged. -/
theorem swap_other_times_invariant (sched : schedule PState) (t1 t2 t : instant) :
    t ≠ t1 → t ≠ t2 → sched t = swapped sched t1 t2 t := by
  intro h1 h2
  rw [swapped_eq, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- The job scheduled at `t2` is scheduled at `t1` after the swap. -/
theorem swap_job_scheduled_t1 (sched : schedule PState) (t1 t2 : instant) (j : Job) :
    scheduled_at (swapped sched t1 t2) j t1 = scheduled_at sched j t2 := by
  unfold scheduled_at; rw [swapped_eq, Equiv.swap_apply_left]

/-- The job scheduled at `t1` is scheduled at `t2` after the swap. -/
theorem swap_job_scheduled_t2 (sched : schedule PState) (t1 t2 : instant) (j : Job) :
    scheduled_at (swapped sched t1 t2) j t2 = scheduled_at sched j t1 := by
  unfold scheduled_at; rw [swapped_eq, Equiv.swap_apply_right]

/-- Scheduling at other times is unchanged. -/
theorem swap_job_scheduled_other_times (sched : schedule PState) (t1 t2 : instant) (j : Job)
    (t : Nat) :
    decide (t1 ≠ t) = true → decide (t2 ≠ t) = true →
      scheduled_at (swapped sched t1 t2) j t = scheduled_at sched j t := by
  intro h1 h2
  unfold scheduled_at
  rw [← swap_other_times_invariant sched t1 t2 t (Ne.symm (of_decide_eq_true h1))
    (Ne.symm (of_decide_eq_true h2))]

/-- Case analysis of scheduling in the swapped schedule. -/
theorem swap_job_scheduled_cases (sched : schedule PState) (t1 t2 : instant) (j : Job)
    (t : instant) :
    scheduled_at (swapped sched t1 t2) j t = true →
      scheduled_at (swapped sched t1 t2) j t = scheduled_at sched j t ∨
        (t = t1 ∧ scheduled_at (swapped sched t1 t2) j t = scheduled_at sched j t2) ∨
        (t = t2 ∧ scheduled_at (swapped sched t1 t2) j t = scheduled_at sched j t1) := by
  intro _
  by_cases h1 : t1 = t
  · subst h1; exact Or.inr (Or.inl ⟨rfl, swap_job_scheduled_t1 sched _ t2 j⟩)
  · by_cases h2 : t2 = t
    · subst h2; exact Or.inr (Or.inr ⟨rfl, swap_job_scheduled_t2 sched t1 _ j⟩)
    · exact Or.inl (swap_job_scheduled_other_times sched t1 t2 j t (decide_eq_true h1)
        (decide_eq_true h2))

/-- A job scheduled in the swapped schedule is scheduled somewhere in the original. -/
theorem swap_job_scheduled (sched : schedule PState) (t1 t2 : instant) (j : Job) (t : instant) :
    scheduled_at (swapped sched t1 t2) j t = true → ∃ t' : instant, scheduled_at sched j t' = true := by
  intro h
  refine ⟨Equiv.swap t1 t2 t, ?_⟩
  unfold scheduled_at at h ⊢
  rwa [swapped_eq] at h

/-- Case analysis of scheduling in the original schedule. -/
theorem swap_job_scheduled_original_cases (sched : schedule PState) (t1 t2 : instant) (j : Job)
    (t : instant) :
    scheduled_at sched j t = true →
      scheduled_at (swapped sched t1 t2) j t = scheduled_at sched j t ∨
        (t = t1 ∧ scheduled_at (swapped sched t1 t2) j t2 = scheduled_at sched j t) ∨
        (t = t2 ∧ scheduled_at (swapped sched t1 t2) j t1 = scheduled_at sched j t) := by
  intro _
  by_cases h1 : t1 = t
  · subst h1; exact Or.inr (Or.inl ⟨rfl, swap_job_scheduled_t2 sched _ t2 j⟩)
  · by_cases h2 : t2 = t
    · subst h2; exact Or.inr (Or.inr ⟨rfl, swap_job_scheduled_t1 sched t1 _ j⟩)
    · exact Or.inl (swap_job_scheduled_other_times sched t1 t2 j t (decide_eq_true h1)
        (decide_eq_true h2))

/-- A job scheduled in the original is scheduled somewhere in the swapped schedule. -/
theorem swap_job_scheduled_original (sched : schedule PState) (t1 t2 : instant) (j : Job)
    (t : instant) :
    scheduled_at sched j t = true → ∃ t' : instant, scheduled_at (swapped sched t1 t2) j t' = true := by
  intro h
  refine ⟨Equiv.swap t1 t2 t, ?_⟩
  unfold scheduled_at at h ⊢
  rwa [swapped_eq, Equiv.swap_apply_self]

/-- Nothing changes before `t1`. -/
theorem swap_before_invariant (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ t : Nat, t < t1 → sched t = swapped sched t1 t2 t := by
  intro hle t ht
  exact swap_other_times_invariant sched t1 t2 t (by omega') (by omega')

/-- Nothing changes after `t2`. -/
theorem swap_after_invariant (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ t : Nat, t2 < t → sched t = swapped sched t1 t2 t := by
  intro hle t ht
  exact swap_other_times_invariant sched t1 t2 t (by omega') (by omega')

/-- The service up to `t ≤ t1` is unchanged. -/
theorem service_before_swap_invariant (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ t : Nat, t ≤ t1 → ∀ j : Job,
      service sched j t = service (swapped sched t1 t2) j t := by
  intro hle t ht j
  unfold service service_during
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Ico] at hx
  unfold service_at
  rw [← swap_before_invariant sched t1 t2 hle x (by omega')]

/-- The service up to `t > t2` is unchanged. -/
theorem service_after_swap_invariant (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ t : Nat, t2 < t → ∀ j : Job,
      service sched j t = service (swapped sched t1 t2) j t := by
  intro hle t ht j
  rw [service_swapped]
  unfold service service_during
  symm
  apply Finset.sum_equiv (Equiv.swap t1 t2)
  · intro x
    simp only [Finset.mem_Ico, Nat.zero_le, true_and]
    constructor
    · intro hx
      by_cases h1 : x = t1
      · subst h1; rw [Equiv.swap_apply_left]; omega'
      · by_cases h2 : x = t2
        · subst h2; rw [Equiv.swap_apply_right]; omega'
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hx
    · intro hx
      by_cases h1 : x = t1
      · omega'
      · by_cases h2 : x = t2
        · omega'
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at hx
  · intro x _
    rfl

/-- Jobs scheduled at neither `t1` nor `t2` receive the same service. -/
theorem service_of_others_invariant (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ (t : instant) (j : Job),
      (!ProcessorState.scheduled_in PState j (sched t1)) = true →
      (!ProcessorState.scheduled_in PState j (sched t2)) = true →
        service sched j t = service (swapped sched t1 t2) j t := by
  intro _ t j h1 h2
  rw [service_swapped]
  unfold service service_during
  apply Finset.sum_congr rfl
  intro x _
  unfold service_at
  by_cases e1 : x = t1
  · subst e1
    rw [Equiv.swap_apply_left, service_in_implies_scheduled_in j _ h1,
      service_in_implies_scheduled_in j _ h2]
  · by_cases e2 : x = t2
    · subst e2
      rw [Equiv.swap_apply_right, service_in_implies_scheduled_in j _ h1,
        service_in_implies_scheduled_in j _ h2]
    · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]

end SwappedFacts

section SwappedScheduleProperties

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

/-- A service bound by the job cost survives the swap. -/
theorem swapped_service_bound [JobCost Job] (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → (∀ (j : Job) (t : instant), service sched j t ≤ job_cost j) →
      ∀ (j : Job) (t : instant), service (swapped sched t1 t2) j t ≤ job_cost j := by
  intro hle hbound j t
  have hmono := service_monotonic (swapped sched t1 t2) j t (max t (t2 + 1)) (Nat.le_max_left _ _)
  rw [← service_after_swap_invariant sched t1 t2 hle (max t (t2 + 1)) (by omega') j] at hmono
  exact Nat.le_trans hmono (hbound j _)

/-- Completed jobs still do not execute after the swap on ideal unit-service
processors. -/
theorem swapped_completed_jobs_dont_execute [JobCost Job] (sched : schedule PState)
    (t1 t2 : instant) :
    t1 ≤ t2 → unit_service_proc_model PState → ideal_progress_proc_model PState →
      completed_jobs_dont_execute sched → completed_jobs_dont_execute (swapped sched t1 t2) := by
  intro hle hunit hideal hcomp
  apply ideal_progress_completed_jobs _ hideal
  exact swapped_service_bound sched t1 t2 hle
    (fun j t => service_at_most_cost sched hcomp j hunit t)

/-- Jobs of the swapped schedule come from the arrival sequence. -/
theorem swapped_jobs_come_from_arrival_sequence (sched : schedule PState) (t1 t2 : instant)
    (arr_seq : arrival_sequence Job) :
    jobs_come_from_arrival_sequence sched arr_seq →
      jobs_come_from_arrival_sequence (swapped sched t1 t2) arr_seq := by
  intro h j t hs
  obtain ⟨t', ht'⟩ := swap_job_scheduled sched t1 t2 j t hs
  exact h j t' ht'

end SwappedScheduleProperties

section EDFSwap

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobDeadline Job]
variable {PState : ProcessorState Job}

/-- Jobs involved in neither allocation still meet their deadlines. -/
theorem uninvolved_implies_deadline_met (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ j : Job, job_meets_deadline sched j = true →
      (!scheduled_at sched j t1) = true → (!scheduled_at sched j t2) = true →
        job_meets_deadline (swapped sched t1 t2) j = true := by
  intro hle j hmet h1 h2
  exact (service_invariant_implies_deadline_met sched (swapped sched t1 t2) j
    (service_of_others_invariant sched t1 t2 hle _ j h1 h2)).mp hmet

/-- The job moved earlier still meets its deadline. -/
theorem moved_earlier_implies_deadline_met (sched : schedule PState) :
    completed_jobs_dont_execute sched →
      ∀ t1 t2 : instant, t1 ≤ t2 → ∀ j : Job, job_meets_deadline sched j = true →
        scheduled_at sched j t2 = true → job_meets_deadline (swapped sched t1 t2) j = true := by
  intro hcomp t1 t2 hle j hmet hs
  have hlater := scheduled_at_implies_later_deadline sched hcomp j t2 hmet hs
  exact (service_invariant_implies_deadline_met sched (swapped sched t1 t2) j
    (service_after_swap_invariant sched t1 t2 hle _ hlater j)).mp hmet

/-- The job moved later still meets its deadline under the EDF-swap conditions. -/
theorem moved_later_implies_deadline_met (sched : schedule PState) (t1 t2 : instant) :
    t1 ≤ t2 →
      (∀ j1 j2 : Job, scheduled_at sched j1 t1 = true → scheduled_at sched j2 t2 = true →
        job_deadline j2 ≤ job_deadline j1) →
      (∀ j1 : Job, scheduled_at sched j1 t1 = true →
        ∃ j2 : Job, scheduled_at sched j2 t2 = true ∧ t2 < job_deadline j2) →
      ∀ j : Job, job_meets_deadline sched j = true → scheduled_at sched j t1 = true →
        job_meets_deadline (swapped sched t1 t2) j = true := by
  intro hle hedf hidle j hmet hs
  obtain ⟨j2, hs2, hdl2⟩ := hidle j hs
  have hle2 := hedf j j2 hs hs2
  exact (service_invariant_implies_deadline_met sched (swapped sched t1 t2) j
    (service_after_swap_invariant sched t1 t2 hle _ (by omega') j)).mp hmet

/-- The EDF swap introduces no deadline misses. -/
theorem edf_swap_no_deadline_misses_introduced (sched : schedule PState) :
    completed_jobs_dont_execute sched →
      ∀ t1 t2 : instant, t1 ≤ t2 →
        (∀ j1 j2 : Job, scheduled_at sched j1 t1 = true → scheduled_at sched j2 t2 = true →
          job_deadline j2 ≤ job_deadline j1) →
        (∀ j1 : Job, scheduled_at sched j1 t1 = true →
          ∃ j2 : Job, scheduled_at sched j2 t2 = true ∧ t2 < job_deadline j2) →
        ∀ j : Job, job_meets_deadline sched j = true →
          job_meets_deadline (swapped sched t1 t2) j = true := by
  intro hcomp t1 t2 hle hedf hidle j hmet
  cases h1 : scheduled_at sched j t1
  · cases h2 : scheduled_at sched j t2
    · exact uninvolved_implies_deadline_met sched t1 t2 hle j hmet (by simp [h1]) (by simp [h2])
    · exact moved_earlier_implies_deadline_met sched hcomp t1 t2 hle j hmet h2
  · exact moved_later_implies_deadline_met sched t1 t2 hle hedf hidle j hmet h1

end EDFSwap

end Prosa.Analysis.Facts.Transform.Swaps
