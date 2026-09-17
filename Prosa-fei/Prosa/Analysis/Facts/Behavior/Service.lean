-- Translated from: ../rt-proofs/analysis/facts/behavior/service.v
import Prosa.Behavior.All
import Prosa.Model.Processor.Platform_properties
import Prosa.Util.Step_function
import Prosa.Util.Sum

namespace Prosa.Analysis.Facts.Behavior.Service

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Platform_properties
open Prosa.Util.Step_function.StepFunction
open Prosa.Util.Sum

section Composition

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (j : Job)

theorem service_during_geq :
    ∀ t1 t2, t1 ≥ t2 → service_during sched j t1 t2 = 0 := by
  intro t1 t2 h
  unfold service_during
  rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]

theorem service0 :
    service sched j 0 = 0 := by
  simp [service, service_during_geq]

theorem service_during_instant :
    ∀ t, service_during sched j t (t + 1) = service_at sched j t := by
  intro t
  unfold service_during
  have hsing : Finset.Ico t (t + 1) = {t} := by ext x; simp
  rw [hsing, Finset.sum_singleton]

theorem service_during_cat :
    ∀ t1 t2 t3,
      t1 ≤ t2 ∧ t2 ≤ t3 →
      service_during sched j t1 t2 + service_during sched j t2 t3 =
        service_during sched j t1 t3 := by
  intro t1 t2 t3 ⟨h12, h23⟩
  simp only [service_during]
  exact Finset.sum_Ico_consecutive (f := fun t => service_at sched j t) h12 h23

theorem service_cat :
    ∀ t1 t2,
      t1 ≤ t2 →
      service sched j t1 + service_during sched j t1 t2 =
        service sched j t2 := by
  intro t1 t2 h
  simp only [service]
  exact service_during_cat sched j 0 t1 t2 ⟨Nat.zero_le _, h⟩

theorem service_during_first_plus_later :
    ∀ t1 t2,
      t1 < t2 →
      service_at sched j t1 + service_during sched j (t1 + 1) t2 =
        service_during sched j t1 t2 := by
  intro t1 t2 h
  rw [← service_during_instant sched j t1]
  exact service_during_cat sched j t1 (t1 + 1) t2 ⟨Nat.le_succ _, h⟩

theorem service_during_last_plus_before :
    ∀ t1 t2,
      t1 ≤ t2 →
      service_during sched j t1 t2 + service_at sched j t2 =
        service_during sched j t1 (t2 + 1) := by
  intro t1 t2 h
  rw [← service_during_instant sched j t2]
  exact service_during_cat sched j t1 t2 (t2 + 1) ⟨h, Nat.le_succ _⟩

theorem service_last_plus_before :
    ∀ t,
      service sched j t + service_at sched j t =
        service sched j (t + 1) := by
  intro t
  simp only [service]
  exact service_during_last_plus_before sched j 0 t (Nat.zero_le _)

theorem service_split_at_point :
    ∀ t1 t2 t3,
      t1 ≤ t2 ∧ t2 < t3 →
      service_during sched j t1 t2 + service_at sched j t2 +
        service_during sched j (t2 + 1) t3 =
        service_during sched j t1 t3 := by
  intro t1 t2 t3 ⟨h12, h23⟩
  rw [Nat.add_assoc, service_during_first_plus_later sched j t2 t3 h23,
      service_during_cat sched j t1 t2 t3 ⟨h12, Nat.le_of_lt h23⟩]

end Composition

section UnitService

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable (H_unit_service : unit_service_proc_model (Job := Job) PState)
variable (sched : schedule PState)
variable (j : Job)

include H_unit_service in
theorem service_at_most_one :
    ∀ t, service_at sched j t ≤ 1 := by
  intro t
  exact H_unit_service j (sched t)

include H_unit_service in
theorem cumulative_service_le_delta :
    ∀ t delta,
      service_during sched j t (t + delta) ≤ delta := by
  intro t delta
  simp only [service_during]
  calc ∑ i ∈ Finset.Ico t (t + delta), service_at sched j i
      ≤ ∑ _i ∈ Finset.Ico t (t + delta), 1 :=
        Finset.sum_le_sum (fun i _ => service_at_most_one H_unit_service sched j i)
    _ = delta := sum_of_ones t delta

section ServiceIsAStepFunction

include H_unit_service in
theorem service_is_a_step_function :
    is_step_function (service sched j) := by
  intro t
  rw [← service_last_plus_before sched j t]
  exact Nat.add_le_add_left (service_at_most_one H_unit_service sched j t) _

variable (t : instant)
variable (s0 : duration)
variable (H_less_than_s : s0 < service sched j t)

include H_unit_service H_less_than_s in
theorem exists_intermediate_service :
    ∃ t0, t0 < t ∧ service sched j t0 = s0 := by
  have h_step := service_is_a_step_function H_unit_service sched j
  have h_s0 : service sched j 0 ≤ s0 ∧ s0 < service sched j t := by
    constructor
    · simp [service, service_during]
    · exact H_less_than_s
  obtain ⟨x_mid, _, hlt, heq⟩ := exists_intermediate_point _ h_step 0 t (Nat.zero_le _) s0 h_s0
  exact ⟨x_mid, hlt, heq⟩

end ServiceIsAStepFunction

end UnitService

section Monotonicity

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (j : Job)

theorem service_monotonic :
    ∀ t1 t2,
      t1 ≤ t2 →
      service sched j t1 ≤ service sched j t2 := by
  intro t1 t2 h
  simp only [service, service_during]
  exact Nat.le.intro (Finset.sum_Ico_consecutive (fun t => service_at sched j t) (Nat.zero_le _) h)

end Monotonicity

section RelationToScheduled

variable {Job : JobType} {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)
variable (j : Job)

theorem not_scheduled_implies_no_service :
    ∀ t,
      scheduled_at sched j t = false → service_at sched j t = 0 := by
  intro t h
  simp only [scheduled_at, ProcessorState.scheduled_in] at h
  simp only [service_at]
  apply ProcessorState.service_implies_scheduled
  simp only [decide_eq_false_iff_not] at h
  exact h

theorem service_at_implies_scheduled_at :
    ∀ t,
      service_at sched j t > 0 → scheduled_at sched j t = true := by
  intro t h
  by_contra hc
  push_neg at hc
  simp only [Bool.not_eq_true] at hc
  have := not_scheduled_implies_no_service sched j t hc
  simp only [work] at h this
  omega

theorem service_delta_implies_scheduled :
    ∀ t,
      service sched j t < service sched j (t + 1) →
        scheduled_at sched j t = true := by
  intro t h
  apply service_at_implies_scheduled_at
  have hcat := service_last_plus_before sched j t
  simp only [work, service, service_during] at h hcat ⊢
  omega

theorem service_during_service_at :
    ∀ t1 t2,
      service_during sched j t1 t2 > 0 ↔
        ∃ t, t1 ≤ t ∧ t < t2 ∧ service_at sched j t > 0 := by
  intro t1 t2
  constructor
  · intro h
    simp only [service_during] at h
    by_contra hall
    push_neg at hall
    have hzero : ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      have := hall i hi.1 hi.2
      simp only [work] at this ⊢
      omega
    simp only [work] at h hzero
    omega
  · rintro ⟨t, ht1, ht2, hserv⟩
    simp only [service_during]
    have hmem : t ∈ Finset.Ico t1 t2 := Finset.mem_Ico.mpr ⟨ht1, ht2⟩
    exact Nat.lt_of_lt_of_le hserv (Finset.single_le_sum (f := fun i => service_at sched j i) (fun _ _ => Nat.zero_le _) hmem)

theorem cumulative_service_implies_scheduled :
    ∀ t1 t2,
      service_during sched j t1 t2 > 0 →
      ∃ t, t1 ≤ t ∧ t < t2 ∧ scheduled_at sched j t = true := by
  intro t1 t2 h
  rw [service_during_service_at] at h
  obtain ⟨t, ht1, ht2, hserv⟩ := h
  exact ⟨t, ht1, ht2, service_at_implies_scheduled_at sched j t hserv⟩

theorem positive_service_implies_scheduled_before :
    ∀ t,
      service sched j t > 0 →
        ∃ t', t' < t ∧ scheduled_at sched j t' = true := by
  intro t h
  simp only [service] at h
  obtain ⟨t', ht1, ht2, hsched⟩ := cumulative_service_implies_scheduled sched j 0 t h
  exact ⟨t', ht2, hsched⟩

section GuaranteedService

variable (H_scheduled_implies_serviced : ideal_progress_proc_model (Job := Job) PState)

include H_scheduled_implies_serviced in
theorem no_service_not_scheduled :
    ∀ t,
      scheduled_at sched j t = false ↔ service_at sched j t = 0 := by
  intro t
  constructor
  · exact not_scheduled_implies_no_service sched j t
  · intro h
    by_contra hc
    push_neg at hc
    simp only [Bool.not_eq_false] at hc
    have hpos : service_at sched j t > 0 := by
      simp only [service_at]
      exact H_scheduled_implies_serviced j (sched t) hc
    simp only [work] at h hpos
    omega

include H_scheduled_implies_serviced in
theorem no_service_during_implies_not_scheduled :
    ∀ t1 t2,
      service_during sched j t1 t2 = 0 →
      ∀ t, t1 ≤ t ∧ t < t2 → scheduled_at sched j t = false := by
  intro t1 t2 hzero t ⟨ht1, ht2⟩
  rw [no_service_not_scheduled sched j H_scheduled_implies_serviced]
  exact (big_nat_eq0 t1 t2 (fun i => service_at sched j i)).mp hzero t ⟨ht1, ht2⟩

include H_scheduled_implies_serviced in
theorem scheduled_implies_cumulative_service :
    ∀ t1 t2,
      (∃ t, t1 ≤ t ∧ t < t2 ∧ scheduled_at sched j t = true) →
      service_during sched j t1 t2 > 0 := by
  intro t1 t2 ⟨t, ht1, ht2, hsched⟩
  rw [service_during_service_at]
  refine ⟨t, ht1, ht2, ?_⟩
  simp only [service_at]
  exact H_scheduled_implies_serviced j (sched t) hsched

include H_scheduled_implies_serviced in
theorem scheduled_implies_nonzero_service :
    ∀ t,
      (∃ t', t' < t ∧ scheduled_at sched j t' = true) →
      service sched j t > 0 := by
  intro t ⟨t', ht, hsched⟩
  simp only [service]
  exact scheduled_implies_cumulative_service sched j H_scheduled_implies_serviced 0 t
    ⟨t', Nat.zero_le _, ht, hsched⟩

end GuaranteedService

section AfterArrival

variable [JobArrival Job]
variable (H_jobs_must_arrive : jobs_must_arrive_to_execute (Job := Job) sched)

include H_jobs_must_arrive in
theorem positive_service_implies_scheduled_since_arrival :
    ∀ t,
      service sched j t > 0 →
      ∃ t', job_arrival j ≤ t' ∧ t' < t ∧ scheduled_at sched j t' = true := by
  intro t h
  obtain ⟨t', ht, hsched⟩ := positive_service_implies_scheduled_before sched j t h
  have harr := H_jobs_must_arrive j t' hsched
  unfold has_arrived at harr
  exact ⟨t', harr, ht, hsched⟩

include H_jobs_must_arrive in
theorem not_scheduled_before_arrival :
    ∀ t, t < job_arrival j → scheduled_at sched j t = false := by
  intro t ht
  by_contra hc
  push_neg at hc
  simp only [Bool.not_eq_false] at hc
  have harr := H_jobs_must_arrive j t hc
  unfold has_arrived at harr
  exact absurd ht (Nat.not_lt.mpr harr)

include H_jobs_must_arrive in
theorem service_before_job_arrival_zero :
    ∀ t,
      t < job_arrival j →
      service_at sched j t = 0 := by
  intro t ht
  exact not_scheduled_implies_no_service sched j t (not_scheduled_before_arrival sched j H_jobs_must_arrive t ht)

include H_jobs_must_arrive in
theorem cumulative_service_before_job_arrival_zero :
    ∀ t1 t2 : instant,
      t2 ≤ job_arrival j →
      service_during sched j t1 t2 = 0 := by
  intro t1 t2 h
  simp only [service_during]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_before_job_arrival_zero sched j H_jobs_must_arrive i (Nat.lt_of_lt_of_le hi.2 h)

include H_jobs_must_arrive in
theorem ignore_service_before_arrival :
    ∀ t1 t2,
      t1 ≤ job_arrival j →
      t2 ≥ job_arrival j →
      service_during sched j t1 t2 = service_during sched j (job_arrival j) t2 := by
  intro t1 t2 h1 h2
  have hcat := service_during_cat sched j t1 (job_arrival j) t2 ⟨h1, h2⟩
  have hzero := cumulative_service_before_job_arrival_zero sched j H_jobs_must_arrive t1 (job_arrival j) (le_refl _)
  simp only [work, service_during] at hcat hzero ⊢
  omega

include H_jobs_must_arrive in
theorem no_service_before_arrival :
    ∀ t,
      t ≤ job_arrival j → service sched j t = 0 := by
  intro t h
  simp only [service]
  exact cumulative_service_before_job_arrival_zero sched j H_jobs_must_arrive 0 t h

end AfterArrival

section TimesWithSameService

variable (t1 t2 : instant)
variable (H_t1_le_t2 : t1 ≤ t2)
variable (H_same_service : service sched j t1 = service sched j t2)

include H_t1_le_t2 H_same_service in
theorem constant_service_implies_no_service_during :
    service_during sched j t1 t2 = 0 := by
  have hcat := service_cat sched j t1 t2 H_t1_le_t2
  simp only [work, service, service_during] at hcat H_same_service ⊢
  omega

include H_t1_le_t2 H_same_service in
theorem constant_service_implies_not_scheduled :
    ∀ t, t1 ≤ t ∧ t < t2 → service_at sched j t = 0 := by
  intro t ⟨ht1, ht2⟩
  have hzero := constant_service_implies_no_service_during sched j t1 t2 H_t1_le_t2 H_same_service
  exact (big_nat_eq0 t1 t2 (fun i => service_at sched j i)).mp hzero t ⟨ht1, ht2⟩

include H_t1_le_t2 H_same_service in
theorem same_service_implies_serviced_at_earlier_times :
    (∃ t : Fin t1, service_at sched j t > 0) ↔
      (∃ t' : Fin t2, service_at sched j t' > 0) := by
  constructor
  · rintro ⟨⟨t, ht⟩, hserv⟩
    exact ⟨⟨t, Nat.lt_of_lt_of_le ht H_t1_le_t2⟩, hserv⟩
  · rintro ⟨⟨t, ht2⟩, hserv⟩
    by_cases ht1 : t < t1
    · exact ⟨⟨t, ht1⟩, hserv⟩
    · exfalso
      push_neg at ht1
      have hns := constant_service_implies_not_scheduled sched j t1 t2 H_t1_le_t2 H_same_service t ⟨ht1, ht2⟩
      simp only [work] at hserv hns
      omega

variable (H_scheduled_implies_serviced : ideal_progress_proc_model (Job := Job) PState)

include H_t1_le_t2 H_same_service H_scheduled_implies_serviced in
theorem same_service_implies_scheduled_at_earlier_times :
    (∃ t : Fin t1, scheduled_at sched j t = true) ↔
      (∃ t' : Fin t2, scheduled_at sched j t' = true) := by
  constructor
  · rintro ⟨⟨t, ht⟩, hsched⟩
    exact ⟨⟨t, Nat.lt_of_lt_of_le ht H_t1_le_t2⟩, hsched⟩
  · rintro ⟨⟨t, ht2⟩, hsched⟩
    by_cases ht1 : t < t1
    · exact ⟨⟨t, ht1⟩, hsched⟩
    · exfalso
      push_neg at ht1
      have hns := constant_service_implies_not_scheduled sched j t1 t2 H_t1_le_t2 H_same_service t ⟨ht1, ht2⟩
      have hpos : service_at sched j t > 0 := by
        simp only [service_at]
        exact H_scheduled_implies_serviced j (sched t) hsched
      simp only [work] at hns hpos
      omega

end TimesWithSameService

end RelationToScheduled

end Prosa.Analysis.Facts.Behavior.Service
