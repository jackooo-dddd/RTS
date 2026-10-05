-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/behavior/completion.v

import Prosa.Model.Job.Properties
import Prosa.Analysis.Facts.Behavior.Service
import Prosa.Analysis.Facts.Behavior.Arrivals
import Prosa.Analysis.Definitions.SchedulePrefix

namespace Prosa.Analysis.Facts.Behavior.Completion

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Arrivals

/-- `omega` after unfolding the time/work aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-! Representation notes: Boolean observations in `Prop` position are
`= true`; `~~ b` is `!b`; single Nat comparisons are the Nat orders;
`a <= b < c` is the Boolean conjunction of decides; `t.+1` is `t + 1`;
`forall s : PState` quantifies over `PState.State`. Binder orders and
hypothesis sets follow the elaborated types (unused section hypotheses are
absent). -/

theorem completion_monotonic {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t t' : Nat, t ≤ t' → completed_by sched j t = true → completed_by sched j t' = true := by
  intro t t' hle hc
  have := service_monotonic sched j t t' hle
  simp only [completed_by, decide_eq_true_eq] at hc ⊢
  omega'

theorem incompletion_monotonic {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t t' : Nat, t ≤ t' → (!completed_by sched j t') = true → (!completed_by sched j t) = true := by
  intro t t' hle hn
  cases hc : completed_by sched j t
  · rfl
  · rw [completion_monotonic sched j t t' hle hc] at hn
    exact absurd hn (by decide)

theorem less_service_than_cost_is_incomplete {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t : instant, service sched j t < job_cost j ↔ (!completed_by sched j t) = true := by
  intro t
  simp only [completed_by, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_le]

theorem incomplete_is_positive_remaining_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t : instant, (!completed_by sched j t) = true ↔ 0 < remaining_cost sched j t := by
  intro t
  rw [← less_service_than_cost_is_incomplete sched j t]
  unfold remaining_cost
  omega'

theorem incomplete_implies_positive_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t : instant, (!completed_by sched j t) = true → job_cost_positive j = true := by
  intro t h
  have := (less_service_than_cost_is_incomplete sched j t).2 h
  simp only [job_cost_positive, decide_eq_true_eq]
  omega'

theorem scheduled_implies_positive_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    completed_jobs_dont_execute sched →
      ∀ t : instant, scheduled_at sched j t = true → 0 < job_cost j := by
  intro hc t hs
  have := hc j t hs
  omega'

theorem service_lt_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    completed_jobs_dont_execute sched →
      ∀ t : instant, scheduled_at sched j t = true → service sched j t < job_cost j :=
  fun hc t hs => hc j t hs

theorem completed_on_arrival_implies_zero_cost {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) :
    jobs_must_arrive_to_execute sched → completed_by sched j (job_arrival j) = true →
      job_cost j = 0 := by
  intro harr hc
  have h0 := no_service_before_arrival sched j harr (job_arrival j) (Nat.le_refl _)
  simp only [completed_by, decide_eq_true_eq] at hc
  omega'

theorem serviced_implies_positive_remaining_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    completed_jobs_dont_execute sched →
      ∀ t : instant, 0 < service_at sched j t → 0 < remaining_cost sched j t := by
  intro hc t hs
  rw [← incomplete_is_positive_remaining_cost, ← less_service_than_cost_is_incomplete]
  exact hc j t (service_at_implies_scheduled_at sched j t hs)

theorem scheduled_implies_serviced {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (j : Job) :
    ideal_progress_proc_model PState →
      ∀ s : PState.State, ProcessorState.scheduled_in PState j s = true →
        0 < ProcessorState.service_in PState j s :=
  fun h s hs => h j s hs

theorem scheduled_implies_positive_remaining_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    completed_jobs_dont_execute sched → ideal_progress_proc_model PState →
      ∀ t : instant, scheduled_at sched j t = true → 0 < remaining_cost sched j t := by
  intro hc hideal t hs
  exact serviced_implies_positive_remaining_cost sched j hc t
    (scheduled_implies_serviced j hideal (sched t) hs)

theorem scheduled_implies_not_completed {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    completed_jobs_dont_execute sched →
      ∀ t : instant, scheduled_at sched j t = true → (!completed_by sched j t) = true := by
  intro hc t hs
  exact (less_service_than_cost_is_incomplete sched j t).1 (hc j t hs)

theorem not_scheduled_remains_incomplete {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t : instant, (!completed_by sched j t) = true → (!scheduled_at sched j t) = true →
      (!completed_by sched j (t + 1)) = true := by
  intro t hn hns
  have h1 := (less_service_than_cost_is_incomplete sched j t).2 hn
  have h2 := not_scheduled_implies_no_service sched j t hns
  have h3 := service_last_plus_before sched j t
  apply (less_service_than_cost_is_incomplete sched j (t + 1)).1
  omega'

theorem completed_implies_not_scheduled {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    completed_jobs_dont_execute sched →
      ∀ t : instant, completed_by sched j t = true → (!scheduled_at sched j t) = true := by
  intro hc t hcomp
  cases hs : scheduled_at sched j t
  · rfl
  · have := scheduled_implies_not_completed sched j hc t hs
    rw [hcomp] at this
    exact absurd this (by decide)

theorem not_pending_earlier_and_at_0 {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    (!pending_earlier_and_at sched j 0) = true := by
  simp [pending_earlier_and_at, arrived_before]

theorem unit_service {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (j : Job) :
    unit_service_proc_model PState →
      ∀ s : PState.State, ProcessorState.service_in PState j s ≤ 1 :=
  fun h s => h j s

theorem service_at_most_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) :
    completed_jobs_dont_execute sched → ∀ j : Job, unit_service_proc_model PState →
      ∀ t : instant, service sched j t ≤ job_cost j := by
  intro hc j hu t
  induction t with
  | zero => rw [service0]; exact Nat.zero_le _
  | succ t ih =>
      rw [← service_last_plus_before]
      rcases Nat.lt_or_ge (service sched j t) (job_cost j) with hlt | hge
      · have := unit_service j hu (sched t)
        change service_at sched j t ≤ 1 at this
        omega'
      · have hcomp : completed_by sched j t = true := by
          simp only [completed_by, decide_eq_true_eq]; omega'
        have hns := completed_implies_not_scheduled sched j hc t hcomp
        rw [not_scheduled_implies_no_service sched j t hns]
        omega'

theorem service_cost_invariant {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) :
    completed_jobs_dont_execute sched → ∀ j : Job, unit_service_proc_model PState →
      ∀ t : instant, service sched j t + remaining_cost sched j t = job_cost j := by
  intro hc j hu t
  have := service_at_most_cost sched hc j hu t
  unfold remaining_cost
  omega'

theorem cumulative_service_le_job_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) :
    completed_jobs_dont_execute sched → ∀ j : Job, unit_service_proc_model PState →
      ∀ t t' : instant, service_during sched j t t' ≤ job_cost j := by
  intro hc j hu t t'
  rcases Nat.le_total t' t with hle | hle
  · rw [service_during_geq sched j t t' hle]; exact Nat.zero_le _
  · have h1 := service_cat sched j t t' hle
    have h2 := service_at_most_cost sched hc j hu t'
    omega'

theorem job_doesnt_complete_before_remaining_cost {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) :
    completed_jobs_dont_execute sched → ∀ j : Job, unit_service_proc_model PState →
      ∀ t : instant, (!completed_by sched j t) = true →
        (!completed_by sched j (t + remaining_cost sched j t - 1)) = true := by
  intro hc j hu t hn
  have hrem := (incomplete_is_positive_remaining_cost sched j t).1 hn
  have hinv := service_cost_invariant sched hc j hu t
  apply (less_service_than_cost_is_incomplete sched j _).1
  have hle : t ≤ t + remaining_cost sched j t - 1 := by omega'
  have hcat := service_cat sched j t _ hle
  have hdelta := cumulative_service_le_delta hu sched j t (remaining_cost sched j t - 1)
  rw [show t + (remaining_cost sched j t - 1) = t + remaining_cost sched j t - 1 by omega'] at hdelta
  omega'

theorem has_arrived_scheduled {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) [JobArrival Job] :
    jobs_must_arrive_to_execute sched →
      ∀ t : instant, scheduled_at sched j t = true → has_arrived j t = true :=
  fun h t hs => h j t hs

theorem scheduled_implies_pending {Job : JobType} [DecidableEq Job] [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) :
    completed_jobs_dont_execute sched → ∀ (j : Job) [JobArrival Job],
      jobs_must_arrive_to_execute sched →
        ∀ t : instant, scheduled_at sched j t = true → pending sched j t = true := by
  intro hc j _ harr t hs
  simp only [pending, Bool.and_eq_true]
  exact ⟨has_arrived_scheduled sched j harr t hs, scheduled_implies_not_completed sched j hc t hs⟩

theorem completed_implies_scheduled_before {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) :
    0 < job_cost j → jobs_must_arrive_to_execute sched →
      ∀ t : instant, completed_by sched j t = true →
        ∃ t' : Nat, (decide (job_arrival j ≤ t') && decide (t' < t)) = true ∧
          scheduled_at sched j t' = true := by
  intro hpos harr t hc
  simp only [completed_by, decide_eq_true_eq] at hc
  exact positive_service_implies_scheduled_since_arrival sched j harr t (by omega')

theorem job_pending_at_arrival {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    0 < job_cost j → jobs_must_arrive_to_execute sched → pending sched j (job_arrival j) = true := by
  intro hpos harr
  have h0 := no_service_before_arrival sched j harr (job_arrival j) (Nat.le_refl _)
  simp only [pending, has_arrived, completed_by, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  refine ⟨Nat.le_refl _, ?_⟩
  omega'

theorem ready_implies_incomplete {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (sched : schedule PState) [JobCost Job] [JobArrival Job]
    [jr : JobReady Job PState] :
    ∀ (j : Job) (t : instant), job_ready sched j t = true → (!completed_by sched j t) = true := by
  intro j t hr
  have := any_ready_job_is_pending sched j t hr
  simp only [pending, Bool.and_eq_true] at this
  exact this.2

theorem completed_jobs_are_not_ready {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (sched : schedule PState) [JobCost Job]
    [JobArrival Job] [jr : JobReady Job PState] :
    jobs_must_be_ready_to_execute sched → completed_jobs_dont_execute sched := by
  intro hready j t hs
  exact (less_service_than_cost_is_incomplete sched j t).2
    (ready_implies_incomplete sched j t (hready j t hs))

theorem valid_schedule_implies_completed_jobs_dont_execute {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [jr : JobReady Job PState] :
    ∀ arr_seq : arrival_sequence Job, valid_schedule sched arr_seq →
      completed_jobs_dont_execute sched := by
  intro arr_seq hv
  exact completed_jobs_are_not_ready sched hv.2

theorem ideal_progress_completed_jobs {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} (sched : schedule PState) [JobCost Job] :
    ideal_progress_proc_model PState →
      (∀ (j : Job) (t : instant), service sched j t ≤ job_cost j) →
        completed_jobs_dont_execute sched := by
  intro hideal hbound j t hs
  have h1 := hbound j (t + 1)
  have h2 := service_last_plus_before sched j t
  have h3 := hideal j (sched t) hs
  change 0 < service_at sched j t at h3
  omega'

theorem identical_prefix_completed_by {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} [jc : JobCost Job] :
    ∀ (sched1 sched2 : schedule PState) (h : instant), identical_prefix sched1 sched2 h →
      ∀ (j : Job) (t : Nat), t ≤ h → completed_by sched1 j t = completed_by sched2 j t := by
  intro sched1 sched2 h hp j t hle
  simp only [completed_by]
  rw [identical_prefix_service sched1 sched2 t (identical_prefix_inclusion sched1 sched2 h t hle hp) j]

theorem identical_prefix_pending {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job} [jc : JobCost Job] [ja : JobArrival Job] :
    ∀ (sched1 sched2 : schedule PState) (h : instant), identical_prefix sched1 sched2 h →
      ∀ (j : Job) (t : Nat), t ≤ h → pending sched1 j t = pending sched2 j t := by
  intro sched1 sched2 h hp j t hle
  simp only [pending]
  rw [identical_prefix_completed_by sched1 sched2 h hp j t hle]

end Prosa.Analysis.Facts.Behavior.Completion
