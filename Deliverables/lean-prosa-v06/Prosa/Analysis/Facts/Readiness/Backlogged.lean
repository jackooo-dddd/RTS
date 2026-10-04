-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/readiness/backlogged.v

import Prosa.Model.Schedule.WorkConserving
import Prosa.Analysis.Facts.Behavior.Arrivals
import Prosa.Analysis.Definitions.Readiness

namespace Prosa.Analysis.Facts.Readiness.Backlogged

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Readiness

/-! Representation notes: `x \in s` in `Prop` position is
`decide (x ∈ s) = true`; `~~ b` is `!b`; a Boolean in `Prop` position is
`= true`; single comparisons are Lean propositions. The readiness model is an
instance binder named as in the source. Binder orders and hypothesis sets
follow the elaborated types. -/

section BackloggedJobs

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job]
variable {PState : ProcessorState Job} [jr : JobReady Job PState]
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)

/-- A backlogged arriving job is among the backlogged jobs. -/
theorem mem_backlogged_jobs :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t : instant), arrives_in arr_seq j → backlogged sched j t = true →
        decide (j ∈ jobs_backlogged_at arr_seq sched t) = true := by
  intro hc j t ha hb
  have hready : job_ready sched j t = true := by
    simp only [backlogged, Bool.and_eq_true] at hb; exact hb.1
  have hpend := ready_implies_pending sched j t hready
  have harr : job_arrival j ≤ t := by
    simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at hpend
    exact hpend.1
  have hbt : arrived_between j 0 (t + 1) = true := by
    simp [arrived_between]; omega
  have hin := arrived_between_implies_in_arrivals arr_seq hc j 0 (t + 1) ha hbt
  unfold jobs_backlogged_at arrivals_up_to
  simp only [decide_eq_true_eq, List.mem_filter] at hin ⊢
  exact ⟨hin, hb⟩

/-- Every backlogged job comes from the arrival sequence. -/
theorem backlogged_job_arrives_in :
    ∀ (j : Job) (t : instant), decide (j ∈ jobs_backlogged_at arr_seq sched t) = true →
      arrives_in arr_seq j := by
  intro j t h
  unfold jobs_backlogged_at arrivals_up_to at h
  simp only [decide_eq_true_eq, List.mem_filter] at h
  exact in_arrivals_implies_arrived arr_seq j 0 (t + 1) (decide_eq_true h.1)

end BackloggedJobs

section NonClairvoyance

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job]
variable {PState : ProcessorState Job} [RM : JobReady Job PState]

/-- Under a nonclairvoyant readiness model, backlog is determined by the
schedule prefix. -/
theorem backlogged_prefix_invariance :
    nonclairvoyant_readiness RM →
      ∀ (sched sched' : schedule PState) (h : instant), identical_prefix sched sched' h →
        ∀ (t : Nat) (j : Job), t < h → backlogged sched j t = backlogged sched' j t := by
  intro hnc sched sched' h hp t j ht
  unfold backlogged
  rw [hnc sched sched' j h hp t (Nat.le_of_lt ht), identical_prefix_scheduled_at sched sched' h hp j t ht]

/-- Variant of the prefix invariance for instants at which the job is not
scheduled in either schedule. -/
theorem backlogged_prefix_invariance' :
    nonclairvoyant_readiness RM →
      ∀ (sched sched' : schedule PState) (h : instant), identical_prefix sched sched' h →
        ∀ (t : instant) (j : Job), (!scheduled_at sched j t) = true →
          (!scheduled_at sched' j t) = true → t ≤ h →
            backlogged sched j t = backlogged sched' j t := by
  intro hnc sched sched' h hp t j hs hs' ht
  unfold backlogged
  rw [hnc sched sched' j h hp t ht]
  simp only [Bool.not_eq_true'] at hs hs'
  rw [hs, hs']

/-- Under a nonclairvoyant readiness model, the backlogged jobs are
determined by the schedule prefix. -/
theorem backlogged_jobs_prefix_invariance :
    nonclairvoyant_readiness RM →
      ∀ (arr_seq : arrival_sequence Job) (sched sched' : schedule PState) (h : instant),
        identical_prefix sched sched' h →
          ∀ t : Nat, t < h → jobs_backlogged_at arr_seq sched t = jobs_backlogged_at arr_seq sched' t := by
  intro hnc arr_seq sched sched' h hp t ht
  unfold jobs_backlogged_at
  apply List.filter_congr
  intro j _
  exact backlogged_prefix_invariance hnc sched sched' h hp t j ht

end NonClairvoyance

end Prosa.Analysis.Facts.Readiness.Backlogged
