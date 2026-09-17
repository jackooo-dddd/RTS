-- Translated from: ../rt-proofs/analysis/facts/model/ideal_schedule.v
import Prosa.Util.All
import Prosa.Model.Processor.Platform_properties
import Prosa.Analysis.Facts.Behavior.Service
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Facts.Model.Ideal_schedule

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Processor.Platform_properties
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Facts.Behavior.Service

section ScheduleClass

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job]
variable [JobCost Job]

attribute [local instance] pstate_instance

theorem ideal_proc_model_is_a_uniprocessor_model :
    uniprocessor_model (Job := Job) (processor_state Job) := by
  intro j1 j2 sched t h1 h2
  unfold scheduled_at ProcessorState.scheduled_in at h1 h2
  simp only [decide_eq_true_eq] at h1 h2
  obtain ⟨_, h1'⟩ := h1
  obtain ⟨_, h2'⟩ := h2
  simp only [ProcessorState.scheduled_on, pstate_instance, ideal_scheduled_at, decide_eq_true_eq] at h1' h2'
  rw [h1'] at h2'; exact Option.some_injective _ h2'

theorem ideal_proc_model_ensures_ideal_progress :
    ideal_progress_proc_model (Job := Job) (processor_state Job) := by
  intro j s h
  unfold ProcessorState.scheduled_in at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨_, h'⟩ := h
  simp only [ProcessorState.scheduled_on, pstate_instance, ideal_scheduled_at, decide_eq_true_eq] at h'
  subst h'
  show 0 < ideal_service_in Job j (some j)
  simp [ideal_service_in]

theorem ideal_proc_model_provides_unit_service :
    unit_service_proc_model (Job := Job) (processor_state Job) := by
  intro j s
  show ideal_service_in Job j s ≤ 1
  unfold ideal_service_in
  split
  · exact Nat.le_refl 1
  · exact Nat.zero_le 1

theorem scheduled_in_def (j : Job) (s : processor_state Job) :
    ProcessorState.scheduled_in j s = decide (s = some j) := by
  unfold ProcessorState.scheduled_in
  simp only [ProcessorState.scheduled_on, ideal_scheduled_at]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨_, h⟩; exact of_decide_eq_true h
  · intro h; exact ⟨(), decide_eq_true h⟩

theorem scheduled_at_def (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t = decide (sched t = some j) := by
  simp only [scheduled_at, scheduled_in_def]

theorem service_in_is_scheduled_in (j : Job) (s : processor_state Job) :
    ProcessorState.service_in j s = if decide (s = some j) then 1 else 0 := by
  simp only [ProcessorState.service_in, pstate_instance, ideal_service_in]

theorem service_at_is_scheduled_at (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    service_at sched j t = if scheduled_at sched j t then 1 else 0 := by
  simp only [service_at, service_in_is_scheduled_in, scheduled_at, scheduled_in_def]

theorem ideal_proc_model_sched_case_analysis
    (sched : schedule (processor_state Job)) (t : instant) :
    is_idle sched t ∨ ∃ j : Job, scheduled_at sched j t = true := by
  simp only [is_idle, scheduled_at_def]
  cases h : sched t with
  | none => left; rfl
  | some j => right; exact ⟨j, by simp [h]⟩

end ScheduleClass

section IncrementalService

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job]
variable [JobCost Job]

attribute [local instance] pstate_instance

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule (processor_state Job))

theorem positive_service_during :
    ∀ (j : Job) (t1 t2 : ℕ),
      0 < service_during sched j t1 t2 →
      ∃ t : ℕ, t1 ≤ t ∧ t < t2 ∧ scheduled_at sched j t = true ∧ service_during sched j t1 t = 0 := by
  intro j t1 t2 SERV
  have LE : t1 ≤ t2 := by
    by_contra h
    simp only [not_le] at h
    have := service_during_geq sched j t1 t2 (Nat.le_of_lt h)
    simp only [work] at this SERV; omega
  by_cases SCHED : scheduled_at sched j t1 = true
  · refine ⟨t1, le_refl _, ?_, SCHED, service_during_geq sched j t1 t1 (le_refl _)⟩
    by_contra h
    simp only [not_lt] at h
    have := service_during_geq sched j t1 t2 h
    simp only [work] at this SERV; omega
  · simp only [Bool.not_eq_true] at SCHED
    have hpos := (service_during_service_at sched j t1 t2).mp SERV
    obtain ⟨t, ht1, ht2, ht_serv⟩ := hpos
    have H_P_at_t : scheduled_at sched j t = true :=
      service_at_implies_scheduled_at sched j t ht_serv
    have H_not_P_at_t1 : ¬ (scheduled_at sched j t1 = true) := by simp [SCHED]
    obtain ⟨x, ⟨hx1, hx2⟩, hx3, hx4⟩ :=
      Prosa.Util.Step_function.StepFunction.exists_first_intermediate_point
        (fun t => scheduled_at sched j t) t1 t ht1 H_not_P_at_t1 H_P_at_t
    refine ⟨x, Nat.le_of_lt hx1, Nat.lt_of_le_of_lt hx2 ht2, hx4, ?_⟩
    apply (Prosa.Util.Sum.big_nat_eq0 t1 x (fun i => service_at sched j i)).mpr
    intro i ⟨hi1, hi2⟩
    have hni : ¬ (scheduled_at sched j i = true) := hx3 i ⟨hi1, hi2⟩
    simp only [Bool.not_eq_true] at hni
    exact not_scheduled_implies_no_service sched j i hni

theorem incremental_service_during :
    ∀ (j : Job) (t1 t2 : ℕ) (k : ℕ),
      service_during sched j t1 t2 > k →
      ∃ t, t1 ≤ t ∧ t < t2 ∧ scheduled_at sched j t = true ∧ service_during sched j t1 t = k := by
  intro j t1 t2 k
  induction k generalizing t2 with
  | zero =>
    intro SERV
    exact positive_service_during sched j t1 t2 SERV
  | succ n ih =>
    intro SERV
    have SERV_n : service_during sched j t1 t2 > n := by
      simp only [work] at SERV ⊢; omega
    obtain ⟨t, ht1, ht2, hSCHED, hSERV⟩ := ih t2 SERV_n
    have hSERV1 : service_during sched j t1 (t + 1) = n + 1 := by
      have hcat := service_during_cat sched j t1 t (t + 1) ⟨ht1, Nat.le_succ t⟩
      rw [hSERV] at hcat
      have hone : service_during sched j t (t + 1) = 1 := by
        rw [service_during_instant]
        rw [service_at_is_scheduled_at]
        simp [hSCHED]
      simp only [work] at hcat hone ⊢; omega
    have hle : t1 ≤ t + 1 := Nat.le_trans ht1 (Nat.le_succ t)
    have hcat2 := service_during_cat sched j t1 (t + 1) t2 ⟨hle, ht2⟩
    rw [hSERV1] at hcat2
    have hrest : 0 < service_during sched j (t + 1) t2 := by
      simp only [work] at hcat2 SERV ⊢; omega
    obtain ⟨t', ht'1, ht'2, hSCHED', hSERV'⟩ := positive_service_during sched j (t + 1) t2 hrest
    refine ⟨t', Nat.le_trans ht1 (Nat.le_of_succ_le ht'1), ht'2, hSCHED', ?_⟩
    have hcat3 := service_during_cat sched j t1 (t + 1) t' ⟨hle, ht'1⟩
    rw [hSERV1, hSERV'] at hcat3
    simp only [work] at hcat3 ⊢; omega

end IncrementalService

end Prosa.Analysis.Facts.Model.Ideal_schedule
