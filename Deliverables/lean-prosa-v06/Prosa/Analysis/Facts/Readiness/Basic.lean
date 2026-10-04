-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/readiness/basic.v

import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Definitions.Readiness
import Prosa.Analysis.Definitions.WorkBearingReadiness

namespace Prosa.Analysis.Facts.Readiness.Basic

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Model.Readiness.Basic
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Readiness
open Prosa.Analysis.Definitions.WorkBearingReadiness

/-! Representation notes: the source enables the section-local
`basic_ready_instance` with `#[local] Existing Instance`; the statements
below pass the accepted Lean definition of the same name explicitly, as the
elaborated source types do. Binder orders and hypothesis sets follow the
elaborated types. -/

/-- LEAN_HELPER: schedules with identical prefixes provide the same service
within the prefix. -/
private theorem service_of_identical_prefix {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched sched' : schedule PState) (h : instant)
    (hp : identical_prefix sched sched' h) (j : Job) (t : instant) (ht : t ≤ h) :
    service sched j t = service sched' j t := by
  unfold service service_during
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < h := by
    simp only [Finset.mem_Ico] at hs
    try dsimp only [instant] at *
    omega
  unfold service_at
  rw [hp s hs']

/-- The basic readiness model is nonclairvoyant. -/
theorem basic_readiness_nonclairvoyance {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job] :
    nonclairvoyant_readiness (basic_ready_instance (PState := PState) (Job := Job)) := by
  intro sched sched' j h hp t ht
  show pending sched j t = pending sched' j t
  unfold pending completed_by
  rw [service_of_identical_prefix sched sched' h hp j t ht]

/-- In the basic model, arrival and completion constraints imply readiness
of scheduled jobs. -/
theorem basic_readiness_compliance {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job] (sched : schedule PState) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      @jobs_must_be_ready_to_execute Job _ _ PState sched _ basic_ready_instance := by
  intro harr hcomp j t hs
  show pending sched j t = true
  have ha := harr j t hs
  have hc := hcomp j t hs
  simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Nat.not_le]
  exact ⟨ha, hc⟩

/-- The basic readiness model is work-bearing for any reflexive JLFP policy. -/
theorem basic_readiness_is_work_bearing_readiness {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [JLFP : JLFP_policy Job] :
    reflexive_job_priorities JLFP →
      @work_bearing_readiness Job _ _ _ PState basic_ready_instance arr_seq sched JLFP := by
  intro hrefl j t ha hp
  exact ⟨j, ha, hp, hrefl j⟩

end Prosa.Analysis.Facts.Readiness.Basic
