-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/behavior/service.v

import Prosa.Util.All
import Prosa.Behavior.All
import Prosa.Analysis.Definitions.SchedulePrefix
import Prosa.Analysis.Facts.Behavior.Supply
import Prosa.Analysis.Facts.Model.Scheduled

namespace Prosa.Analysis.Facts.Behavior.Service

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Analysis.Definitions.Service
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Util.UnitGrowth
open scoped BigOperators

/-- `omega'` after unfolding the time/work aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-! Representation notes (as in the accepted facts files): MathComp's
Boolean chains `a <= b < c` are `(decide (a ≤ b) && decide (b < c)) = true`;
`~~ b` in Prop position is `(!b) = true`; `x \in xs` is `decide (x ∈ xs) = true`;
the finite Boolean existential `[exists t : 'I_n, p t]` is
`(List.range' 0 n).any p` (the same list as MathComp's `iota 0 n`). -/

/-! ## Composition -/

section Composition

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
variable (sched : schedule PState) (j : Job)

theorem service_during_geq :
    ∀ t1 t2 : Nat, t2 ≤ t1 → service_during sched j t1 t2 = 0 := by
  intro t1 t2 h
  simp [service_during, Finset.Ico_eq_empty_of_le h]

theorem service_during_ge :
    ∀ (t1 t2 : instant) (k : Nat), k < service_during sched j t1 t2 → t1 < t2 := by
  intro t1 t2 k h
  by_contra hne
  have := service_during_geq sched j t1 t2 (by omega')
  omega'

theorem service0 : service sched j 0 = 0 := by
  simp [service, service_during]

theorem service_during_instant :
    ∀ t : instant, service_during sched j t (t + 1) = service_at sched j t := by
  intro t
  simp [service_during]

theorem service_during_cat :
    ∀ t1 t2 t3 : Nat, (decide (t1 ≤ t2) && decide (t2 ≤ t3)) = true →
      service_during sched j t1 t2 + service_during sched j t2 t3 =
        service_during sched j t1 t3 := by
  intro t1 t2 t3 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Finset.sum_Ico_consecutive _ h.1 h.2

theorem service_cat :
    ∀ t1 t2 : Nat, t1 ≤ t2 →
      service sched j t1 + service_during sched j t1 t2 = service sched j t2 := by
  intro t1 t2 h
  exact service_during_cat sched j 0 t1 t2 (by simp [h])

theorem service_during_first_plus_later :
    ∀ t1 t2 : Nat, t1 < t2 →
      service_at sched j t1 + service_during sched j (t1 + 1) t2 =
        service_during sched j t1 t2 := by
  intro t1 t2 h
  rw [← service_during_instant sched j t1]
  exact service_during_cat sched j t1 (t1 + 1) t2 (by simp; omega')

theorem service_during_last_plus_before :
    ∀ t1 t2 : Nat, t1 ≤ t2 →
      service_during sched j t1 t2 + service_at sched j t2 =
        service_during sched j t1 (t2 + 1) := by
  intro t1 t2 h
  rw [← service_during_instant sched j t2]
  exact service_during_cat sched j t1 t2 (t2 + 1) (by simp; omega')

theorem service_last_plus_before :
    ∀ t : instant, service sched j t + service_at sched j t = service sched j (t + 1) := by
  intro t
  exact service_during_last_plus_before sched j 0 t (Nat.zero_le t)

theorem service_split_at_point :
    ∀ t1 t2 t3 : Nat, (decide (t1 ≤ t2) && decide (t2 < t3)) = true →
      service_during sched j t1 t2 + service_at sched j t2 +
          service_during sched j (t2 + 1) t3 = service_during sched j t1 t3 := by
  intro t1 t2 t3 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Nat.add_assoc, service_during_first_plus_later sched j t2 t3 h.2]
  exact service_during_cat sched j t1 t2 t3 (by simp; omega')

end Composition

/-! ## Unit service -/

section UnitService

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

theorem service_at_most_one (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t : instant), service_at sched j t ≤ 1 :=
  fun sched j t => H_unit_service j (sched t)

theorem service_is_zero_or_one (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t : instant),
      service_at sched j t = 0 ∨ service_at sched j t = 1 := by
  intro sched j t
  have := service_at_most_one H_unit_service sched j t
  omega'

private theorem service_during_le_length (H_unit_service : unit_service_proc_model PState)
    (sched : schedule PState) (j : Job) (t1 t2 : Nat) :
    service_during sched j t1 t2 ≤ t2 - t1 := by
  unfold service_during
  calc ∑ t ∈ Finset.Ico t1 t2, service_at sched j t
      ≤ ∑ _t ∈ Finset.Ico t1 t2, 1 :=
        Finset.sum_le_sum (fun t _ => service_at_most_one H_unit_service sched j t)
    _ = t2 - t1 := by simp

theorem cumulative_service_le_delta (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t : instant) (delta : Nat),
      service_during sched j t (t + delta) ≤ delta := by
  intro sched j t delta
  have := service_during_le_length H_unit_service sched j t (t + delta)
  omega'

theorem cumulative_service_ge_delta (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t : instant) (delta ρ : Nat),
      ρ ≤ service_during sched j t (t + delta) → ρ ≤ delta := by
  intro sched j t delta ρ h
  exact Nat.le_trans h (cumulative_service_le_delta H_unit_service sched j t delta)

theorem service_during_is_unit_growth_function
    (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t0 : instant),
      unit_growth_function (service_during sched j t0) := by
  intro sched j t0 t
  by_cases h : t0 ≤ t
  · rw [← service_during_last_plus_before sched j t0 t h]
    have := service_at_most_one H_unit_service sched j t
    omega'
  · rw [service_during_geq sched j t0 t (by omega')]
    have := service_during_le_length H_unit_service sched j t0 (t + 1)
    omega'

theorem service_is_unit_growth_function (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job), unit_growth_function (service sched j) :=
  fun sched j => service_during_is_unit_growth_function H_unit_service sched j 0

theorem exists_intermediate_service_during
    (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t0 t1 t2 s : Nat),
      (decide (t0 ≤ t1) && decide (t1 ≤ t2)) = true →
      (decide (service_during sched j t0 t1 ≤ s) &&
          decide (s < service_during sched j t0 t2)) = true →
      ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧
        service_during sched j t0 t = s := by
  intro sched j t0 t1 t2 s h12 hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h12 hs
  obtain ⟨t, ht, heq⟩ := exists_intermediate_point (service_during sched j t0)
    (service_during_is_unit_growth_function H_unit_service sched j t0) t1 t2 h12.2 s hs
  exact ⟨t, by simp [ht.1, ht.2], heq⟩

theorem exists_intermediate_service (H_unit_service : unit_service_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t : instant) (s : duration),
      s < service sched j t → ∃ t' : Nat, t' < t ∧ service sched j t' = s := by
  intro sched j t s h
  obtain ⟨t', ht', heq⟩ := exists_intermediate_service_during H_unit_service sched j 0 0 t s
    (by simp) (by simp [service0, service] at h ⊢; exact ⟨by rw [service_during_geq sched j 0 0 (le_refl 0)]; omega', h⟩)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  exact ⟨t', ht'.2, heq⟩

end UnitService

/-! ## Fully consuming processors -/

theorem ideal_progress_inside_supplies {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job}
    (H_consumed_supply_proc_model : fully_consuming_proc_model PState) :
    ∀ (sched : schedule PState) (j : Job) (t : instant),
      has_supply sched t = true → scheduled_at sched j t = true →
        receives_service_at sched j t = true := by
  intro sched j t hsup hsched
  have heq := H_consumed_supply_proc_model j sched t hsched
  simp only [has_supply, decide_eq_true_eq] at hsup
  simp only [receives_service_at, decide_eq_true_eq]
  omega'

/-! ## Monotonicity -/

theorem service_monotonic {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) :
    ∀ t1 t2 : Nat, t1 ≤ t2 → service sched j t1 ≤ service sched j t2 := by
  intro t1 t2 h
  rw [← service_cat sched j t1 t2 h]
  omega'

/-! ## Relation to `scheduled_in` / `scheduled_at` -/

section RelationToScheduled

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

theorem service_in_implies_scheduled_in (j : Job) :
    ∀ s : PState.State, (!ProcessorState.scheduled_in PState j s) = true →
      ProcessorState.service_in PState j s = 0 := by
  intro s h
  have hnot : ∀ c : PState.Core, PState.scheduled_on j s c = false := by
    intro c
    cases hc : PState.scheduled_on j s c with
    | false => rfl
    | true =>
        have : ProcessorState.scheduled_in PState j s = true :=
          (ProcessorState.scheduled_in_eq_true_iff PState j s).mpr ⟨c, hc⟩
        simp [this] at h
  unfold ProcessorState.service_in
  exact Finset.sum_eq_zero (fun c _ => PState.service_on_implies_scheduled_on j s c (hnot c))

variable (sched : schedule PState) (j : Job)

theorem not_scheduled_implies_no_service :
    ∀ t : instant, (!scheduled_at sched j t) = true → service_at sched j t = 0 :=
  fun t h => service_in_implies_scheduled_in j (sched t) h

private theorem scheduled_of_pos_service (t : instant) (h : 0 < service_at sched j t) :
    scheduled_at sched j t = true := by
  cases hs : scheduled_at sched j t with
  | true => rfl
  | false =>
      have := not_scheduled_implies_no_service sched j t (by simp [hs])
      omega'

theorem not_scheduled_during_implies_zero_service :
    ∀ t1 t2 : Nat,
      (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → (!scheduled_at sched j t) = true) →
      service_during sched j t1 t2 = 0 := by
  intro t1 t2 h
  unfold service_during
  refine Finset.sum_eq_zero (fun t ht => ?_)
  rw [Finset.mem_Ico] at ht
  exact not_scheduled_implies_no_service sched j t (h t (by simp [ht.1, ht.2]))

theorem service_at_implies_scheduled_at :
    ∀ t : instant, 0 < service_at sched j t → scheduled_at sched j t = true :=
  fun t h => scheduled_of_pos_service sched j t h

theorem service_delta_implies_scheduled :
    ∀ t : instant, service sched j t < service sched j (t + 1) → scheduled_at sched j t = true := by
  intro t h
  rw [← service_last_plus_before sched j t] at h
  exact scheduled_of_pos_service sched j t (by omega')

theorem service_during_service_at :
    ∀ t1 t2 : instant, 0 < service_during sched j t1 t2 ↔
      ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ 0 < service_at sched j t := by
  intro t1 t2
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hz : service_during sched j t1 t2 = 0 := by
      unfold service_during
      refine Finset.sum_eq_zero (fun t ht => ?_)
      rw [Finset.mem_Ico] at ht
      have := hne t (by simp [ht.1, ht.2])
      omega'
    omega'
  · rintro ⟨t, ht, hpos⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    unfold service_during
    exact Nat.lt_of_lt_of_le hpos
      (Finset.single_le_sum (f := fun t => service_at sched j t) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.mpr ht))

theorem cumulative_service_implies_scheduled :
    ∀ t1 t2 : instant, 0 < service_during sched j t1 t2 →
      ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ scheduled_at sched j t = true := by
  intro t1 t2 h
  obtain ⟨t, ht, hpos⟩ := (service_during_service_at sched j t1 t2).mp h
  exact ⟨t, ht, scheduled_of_pos_service sched j t hpos⟩

theorem positive_service_implies_scheduled_before :
    ∀ t : instant, 0 < service sched j t → ∃ t' : Nat, t' < t ∧ scheduled_at sched j t' = true := by
  intro t h
  obtain ⟨t', ht', hs⟩ := cumulative_service_implies_scheduled sched j 0 t h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  exact ⟨t', ht'.2, hs⟩

/-- The earliest instant in `[t1, t2)` with positive service. -/
private theorem earliest_service (t1 t2 : instant) (h : 0 < service_during sched j t1 t2) :
    ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ 0 < service_at sched j t ∧
      service_during sched j t1 t = 0 := by
  classical
  obtain ⟨t0, ht0, hpos0⟩ := (service_during_service_at sched j t1 t2).mp h
  have hex : ∃ t, t1 ≤ t ∧ t < t2 ∧ 0 < service_at sched j t := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht0
    exact ⟨t0, ht0.1, ht0.2, hpos0⟩
  obtain ⟨tm, hspec, hmin⟩ : ∃ tm, (t1 ≤ tm ∧ tm < t2 ∧ 0 < service_at sched j tm) ∧
      ∀ t < tm, ¬ (t1 ≤ t ∧ t < t2 ∧ 0 < service_at sched j t) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  refine ⟨tm, by simp [hspec.1, hspec.2.1], hspec.2.2, ?_⟩
  unfold service_during
  refine Finset.sum_eq_zero (fun t ht => ?_)
  rw [Finset.mem_Ico] at ht
  have := hmin t ht.2
  have : ¬ 0 < service_at sched j t := fun hp => this ⟨ht.1, by omega', hp⟩
  omega'

theorem service_during_service_at_earliest :
    ∀ t1 t2 : instant, 0 < service_during sched j t1 t2 →
      ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ 0 < service_at sched j t ∧
        service_during sched j t1 t = 0 :=
  fun t1 t2 h => earliest_service sched j t1 t2 h

theorem service_during_scheduled_at_earliest :
    ∀ t1 t2 : instant, 0 < service_during sched j t1 t2 →
      ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ scheduled_at sched j t = true ∧
        service_during sched j t1 t = 0 := by
  intro t1 t2 h
  obtain ⟨t, ht, hpos, hz⟩ := earliest_service sched j t1 t2 h
  exact ⟨t, ht, scheduled_of_pos_service sched j t hpos, hz⟩

section GuaranteedService

theorem no_service_not_scheduled (H_scheduled_implies_serviced : ideal_progress_proc_model PState) :
    ∀ t : instant, (!scheduled_at sched j t) = true ↔ service_at sched j t = 0 := by
  intro t
  constructor
  · exact not_scheduled_implies_no_service sched j t
  · intro h
    cases hs : scheduled_at sched j t with
    | false => rfl
    | true =>
        have := H_scheduled_implies_serviced j (sched t) hs
        unfold service_at at h
        omega'

theorem no_service_during_implies_not_scheduled
    (H_scheduled_implies_serviced : ideal_progress_proc_model PState) :
    ∀ t1 t2 : instant, service_during sched j t1 t2 = 0 →
      ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → (!scheduled_at sched j t) = true := by
  intro t1 t2 hz t ht
  refine (no_service_not_scheduled sched j H_scheduled_implies_serviced t).mpr ?_
  by_contra hne
  have : 0 < service_during sched j t1 t2 :=
    (service_during_service_at sched j t1 t2).mpr ⟨t, ht, by omega'⟩
  omega'

theorem scheduled_implies_cumulative_service
    (H_scheduled_implies_serviced : ideal_progress_proc_model PState) :
    ∀ t1 t2 : Nat,
      (∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ scheduled_at sched j t = true) →
      0 < service_during sched j t1 t2 := by
  rintro t1 t2 ⟨t, ht, hs⟩
  exact (service_during_service_at sched j t1 t2).mpr
    ⟨t, ht, H_scheduled_implies_serviced j (sched t) hs⟩

theorem scheduled_implies_nonzero_service
    (H_scheduled_implies_serviced : ideal_progress_proc_model PState) :
    ∀ t : Nat, (∃ t' : Nat, t' < t ∧ scheduled_at sched j t' = true) → 0 < service sched j t := by
  rintro t ⟨t', ht', hs⟩
  exact scheduled_implies_cumulative_service sched j H_scheduled_implies_serviced 0 t
    ⟨t', by simp [ht'], hs⟩

theorem unit_service_at1 (H_scheduled_implies_serviced : ideal_progress_proc_model PState)
    (H_unit : unit_service_proc_model PState) :
    ∀ t : instant, scheduled_at sched j t = true → service_at sched j t = 1 := by
  intro t hs
  have h1 := H_scheduled_implies_serviced j (sched t) hs
  have h2 := H_unit j (sched t)
  unfold service_at
  omega'

end GuaranteedService

section AfterArrival

variable [JobArrival Job]

theorem not_scheduled_before_arrival (H_jobs_must_arrive : jobs_must_arrive_to_execute sched) :
    ∀ t : Nat, t < job_arrival j → (!scheduled_at sched j t) = true := by
  intro t ht
  cases hs : scheduled_at sched j t with
  | false => rfl
  | true =>
      have := H_jobs_must_arrive j t hs
      simp only [has_arrived, decide_eq_true_eq] at this
      omega'

theorem positive_service_implies_scheduled_since_arrival
    (H_jobs_must_arrive : jobs_must_arrive_to_execute sched) :
    ∀ t : instant, 0 < service sched j t →
      ∃ t' : Nat, (decide (job_arrival j ≤ t') && decide (t' < t)) = true ∧
        scheduled_at sched j t' = true := by
  intro t h
  obtain ⟨t', ht', hs⟩ := positive_service_implies_scheduled_before sched j t h
  have harr := H_jobs_must_arrive j t' hs
  simp only [has_arrived, decide_eq_true_eq] at harr
  exact ⟨t', by simp [harr, ht'], hs⟩

theorem service_before_job_arrival_zero (H_jobs_must_arrive : jobs_must_arrive_to_execute sched) :
    ∀ t : Nat, t < job_arrival j → service_at sched j t = 0 :=
  fun t ht => not_scheduled_implies_no_service sched j t
    (not_scheduled_before_arrival sched j H_jobs_must_arrive t ht)

theorem cumulative_service_before_job_arrival_zero
    (H_jobs_must_arrive : jobs_must_arrive_to_execute sched) :
    ∀ t1 t2 : instant, t2 ≤ job_arrival j → service_during sched j t1 t2 = 0 := by
  intro t1 t2 h
  unfold service_during
  refine Finset.sum_eq_zero (fun t ht => ?_)
  rw [Finset.mem_Ico] at ht
  exact service_before_job_arrival_zero sched j H_jobs_must_arrive t (by omega')

theorem ignore_service_before_arrival (H_jobs_must_arrive : jobs_must_arrive_to_execute sched) :
    ∀ t1 t2 : Nat, t1 ≤ job_arrival j → job_arrival j ≤ t2 →
      service_during sched j t1 t2 = service_during sched j (job_arrival j) t2 := by
  intro t1 t2 h1 h2
  rw [← service_during_cat sched j t1 (job_arrival j) t2 (by simp [h1, h2]),
    cumulative_service_before_job_arrival_zero sched j H_jobs_must_arrive t1 (job_arrival j) le_rfl]
  simp

theorem no_service_before_arrival (H_jobs_must_arrive : jobs_must_arrive_to_execute sched) :
    ∀ t : Nat, t ≤ job_arrival j → service sched j t = 0 :=
  fun t h => cumulative_service_before_job_arrival_zero sched j H_jobs_must_arrive 0 t h

end AfterArrival

section TimesWithSameService

theorem constant_service_implies_no_service_during :
    ∀ t1 t2 : instant, t1 ≤ t2 → service sched j t1 = service sched j t2 →
      service_during sched j t1 t2 = 0 := by
  intro t1 t2 hle heq
  have := service_cat sched j t1 t2 hle
  omega'

theorem constant_service_implies_not_scheduled :
    ∀ t1 t2 : instant, t1 ≤ t2 → service sched j t1 = service sched j t2 →
      ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → service_at sched j t = 0 := by
  intro t1 t2 hle heq t ht
  have hz := constant_service_implies_no_service_during sched j t1 t2 hle heq
  by_contra hne
  have := (service_during_service_at sched j t1 t2).mpr ⟨t, ht, by omega'⟩
  omega'

private theorem any_range_mono_iff (P : Nat → Bool) (t1 t2 : Nat) (hle : t1 ≤ t2)
    (hmid : ∀ t, t1 ≤ t → t < t2 → P t = false) :
    (List.range' 0 t1).any P = (List.range' 0 t2).any P := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range'_1, Nat.zero_add, Nat.zero_le, true_and]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, by omega', hp⟩
  · rintro ⟨t, ht, hp⟩
    by_cases h : t < t1
    · exact ⟨t, h, hp⟩
    · rw [hmid t (by omega') ht] at hp
      exact absurd hp (by simp)

theorem same_service_implies_serviced_at_earlier_times :
    ∀ t1 t2 : instant, t1 ≤ t2 → service sched j t1 = service sched j t2 →
      (List.range' 0 t1).any (fun t => decide (0 < service_at sched j t)) =
        (List.range' 0 t2).any (fun t => decide (0 < service_at sched j t)) := by
  intro t1 t2 hle heq
  apply any_range_mono_iff _ t1 t2 hle
  intro t h1 h2
  have := constant_service_implies_not_scheduled sched j t1 t2 hle heq t (by simp [h1, h2])
  simp [this]

theorem same_service_implies_scheduled_at_earlier_times :
    ∀ t1 t2 : instant, t1 ≤ t2 → service sched j t1 = service sched j t2 →
      ideal_progress_proc_model PState →
      (List.range' 0 t1).any (fun t => scheduled_at sched j t) =
        (List.range' 0 t2).any (fun t => scheduled_at sched j t) := by
  intro t1 t2 hle heq hideal
  apply any_range_mono_iff _ t1 t2 hle
  intro t h1 h2
  have hz := constant_service_implies_not_scheduled sched j t1 t2 hle heq t (by simp [h1, h2])
  have := (no_service_not_scheduled sched j hideal t).mpr hz
  simpa using this

end TimesWithSameService

end RelationToScheduled

/-! ## Generic processor -/

section GenericProcessor

variable {Job : JobType} [DecidableEq Job]

theorem receives_service_and_served_at_consistent [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (H_valid_arrival_sequence : valid_arrival_sequence arr_seq) :
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (j : Job) (t : instant), receives_service_at sched j t = true →
        decide (j ∈ served_jobs_at arr_seq sched t) = true := by
  intro sched hfrom hmust j t hrec
  have hs : scheduled_at sched j t = true :=
    service_at_implies_scheduled_at sched j t (by
      simpa only [receives_service_at, decide_eq_true_eq] using hrec)
  have hup := Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_up_to_scheduled_at arr_seq
    H_valid_arrival_sequence.1 sched hfrom hmust j t hs t (Nat.le_refl _)
  simp only [decide_eq_true_eq] at hup ⊢
  simp only [served_jobs_at, List.mem_filter]
  exact ⟨hup, hrec⟩

theorem served_at_and_receives_service_consistent {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (j : Job) (t : instant) :
    decide (j ∈ served_jobs_at arr_seq sched t) = true → receives_service_at sched j t = true := by
  intro h
  simp only [decide_eq_true_eq, served_jobs_at, List.mem_filter] at h
  exact h.2

theorem no_service_received_when_idle [JobArrival Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (H_valid_arrival_sequence : valid_arrival_sequence arr_seq) :
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (j : Job) (t : instant), is_idle arr_seq sched t = true →
        (!receives_service_at sched j t) = true := by
  intro sched hfrom hmust j t hidle
  have hns := Prosa.Analysis.Facts.Model.Scheduled.not_scheduled_when_idle arr_seq
    H_valid_arrival_sequence sched hfrom hmust j t hidle
  have hz := not_scheduled_implies_no_service sched j t hns
  simp [receives_service_at, hz]

theorem receives_service_implies_has_supply {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) :
    receives_service_at sched j t = true → has_supply sched t = true := by
  intro h
  simp only [receives_service_at, decide_eq_true_eq] at h
  have := Prosa.Analysis.Facts.Behavior.Supply.service_at_le_supply_at sched j t
  simp only [has_supply, decide_eq_true_eq]
  omega'

theorem no_blackout_when_service_received {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) :
    receives_service_at sched j t = true → (!is_blackout sched t) = true := by
  intro h
  simp [is_blackout, receives_service_implies_has_supply sched j t h]

theorem no_service_during_blackout {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) :
    is_blackout sched t = true → service_at sched j t = 0 := by
  intro h
  by_contra hne
  have := no_blackout_when_service_received sched j t (by
    simp only [receives_service_at, decide_eq_true_eq]; omega')
  simp [h] at this

end GenericProcessor

/-! ## Uniprocessor -/

theorem only_one_job_receives_service_at_uni {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (H_uniprocessor_proc_model : uniprocessor_model PState) :
    ∀ (sched : schedule PState) (j1 j2 : Job) (t : instant),
      receives_service_at sched j1 t = true → receives_service_at sched j2 t = true → j1 = j2 := by
  intro sched j1 j2 t h1 h2
  simp only [receives_service_at, decide_eq_true_eq] at h1 h2
  exact H_uniprocessor_proc_model j1 j2 sched t
    (service_at_implies_scheduled_at sched j1 t h1) (service_at_implies_scheduled_at sched j2 t h2)

/-! ## Incremental service -/

theorem incremental_service_during {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    (H_unit_service : unit_service_proc_model PState) :
    ∀ (j : Job) (t1 t2 : instant) (k : Nat), k < service_during sched j t1 t2 →
      ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ scheduled_at sched j t = true ∧
        service_during sched j t1 t = k := by
  classical
  intro j t1 t2 k h
  have hlt : t1 < t2 := service_during_ge sched j t1 t2 k h
  have hex : ∃ d, k < service_during sched j t1 (t1 + d) := ⟨t2 - t1, by
    rwa [Nat.add_sub_cancel' (Nat.le_of_lt hlt)]⟩
  obtain ⟨d, hd, hmin⟩ : ∃ d, k < service_during sched j t1 (t1 + d) ∧
      ∀ d' < d, ¬ k < service_during sched j t1 (t1 + d') :=
    ⟨Nat.find hex, Nat.find_spec hex, fun d' hd' => Nat.find_min hex hd'⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := service_during_geq sched j t1 t1 le_rfl
    simp only [Nat.add_zero] at hd
    omega'
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega'⟩
  have hprev := hmin d' (by omega')
  have hstep := service_during_last_plus_before sched j t1 (t1 + d') (by omega')
  have hone := service_at_most_one H_unit_service sched j (t1 + d')
  have hk : service_during sched j t1 (t1 + d') = k := by
    rw [show t1 + (d' + 1) = t1 + d' + 1 by omega'] at hd
    omega'
  have hle2 : t1 + d' < t2 := by
    by_contra hge
    have := service_during_cat sched j t1 t2 (t1 + d') (by simp; omega')
    rw [show t1 + (d' + 1) = t1 + d' + 1 by omega'] at hd
    have hmono := service_during_cat sched j t1 t2 (t1 + d' + 1) (by simp; omega')
    have := hmin (t2 - t1) (by omega')
    rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)] at this
    exact this h
  refine ⟨t1 + d', by simp; omega', ?_, hk⟩
  apply service_at_implies_scheduled_at
  rw [show t1 + (d' + 1) = t1 + d' + 1 by omega'] at hd
  omega'

theorem kth_scheduling_time {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ (t t' : instant) (k : Nat), service sched j t = k → k < service sched j t' →
      ∃ st : Nat, (decide (t ≤ st) && decide (st < t')) = true ∧ service sched j st = k ∧
        scheduled_at sched j st = true := by
  classical
  intro t t' k hk hlt
  have htt' : t < t' := by
    by_contra hge
    have := service_monotonic sched j t' t (by omega')
    omega'
  have hsearch : ∃ n, t ≤ t' - (n + 1) ∧ service sched j (t' - (n + 1)) = k ∧
      service sched j (t' - n) > k := by
    have hP0 : service sched j (t' - 0) > k := by simpa using hlt
    have hPt : ¬ service sched j (t' - (t' - t)) > k := by
      rw [show t' - (t' - t) = t by omega']; omega'
    obtain ⟨n, hn, hn1⟩ : ∃ n, service sched j (t' - n) > k ∧ ¬ service sched j (t' - (n + 1)) > k := by
      by_contra hno
      push Not at hno
      have : ∀ n, service sched j (t' - n) > k := by
        intro n
        induction n with
        | zero => exact hP0
        | succ n ih => exact hno n ih
      exact hPt (this (t' - t))
    have hge : t ≤ t' - (n + 1) := by
      by_contra hlt'
      have : t' - n ≤ t := by omega'
      have := service_monotonic sched j (t' - n) t this
      omega'
    have hmono := service_monotonic sched j t (t' - (n + 1)) hge
    exact ⟨n, hge, by omega', hn⟩
  obtain ⟨n, hge, hkeq, hgt⟩ := hsearch
  have hn : n < t' := by
    by_contra hnot
    have heqn : t' - n = t' - (n + 1) := by omega'
    rw [heqn] at hgt
    omega'
  refine ⟨t' - (n + 1), ?_, hkeq, ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega'
  apply service_delta_implies_scheduled
  rw [show t' - (n + 1) + 1 = t' - n by omega']
  omega'

/-! ## Service in two schedules -/

section ServiceInTwoSchedules

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
variable (sched1 sched2 : schedule PState)

theorem same_service_during (t1 t2 : instant) (j : Job) :
    (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
        service_at sched1 j t = service_at sched2 j t) →
      service_during sched1 j t1 t2 = service_during sched2 j t1 t2 := by
  intro h
  unfold service_during
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_Ico] at ht
  exact h t (by simp [ht.1, ht.2])

theorem equal_prefix_implies_same_service_during :
    ∀ t1 t2 : Nat, (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → sched1 t = sched2 t) →
      ∀ j : Job, service_during sched1 j t1 t2 = service_during sched2 j t1 t2 := by
  intro t1 t2 h j
  exact same_service_during sched1 sched2 t1 t2 j (fun t ht => by
    simp only [service_at, h t ht])

theorem identical_prefix_service :
    ∀ h : instant, identical_prefix sched1 sched2 h →
      ∀ j : Job, service sched1 j h = service sched2 j h := by
  intro h hp j
  exact equal_prefix_implies_same_service_during sched1 sched2 0 h (fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact hp t ht.2) j

end ServiceInTwoSchedules

end Prosa.Analysis.Facts.Behavior.Service
