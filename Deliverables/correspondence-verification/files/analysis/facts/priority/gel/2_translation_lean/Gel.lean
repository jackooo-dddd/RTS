-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/gel.v

import Prosa.Util.Int
import Prosa.Model.Priority.Gel
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Facts.Priority.Sequential

namespace Prosa.Analysis.Facts.Priority.Gel

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.AlwaysHigherPriority
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Priority.Sequential

/-! Basic facts about the GEL policy.

Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
The source's exported `GEL` instance is the accepted reducible definition,
passed explicitly as the JLFP policy wherever the elaborated statements
resolve it. Representation (as in the accepted `model/priority/gel.v`):
MathComp's `int` is Lean's `Int`, `n%:R` is the cast `(n : Int)`, and
`(a <= b)%R` is `decide (a ≤ b)`; a Boolean in `Prop` position is `= true`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

section GELBasicFacts

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- Under GEL, `hep_job` compares absolute priority points. -/
theorem hep_job_priority_point [JobTask Job Task] [PriorityPoint Task] [Arrival : JobArrival Job] :
    ∀ j j' : Job,
      (GEL Job Task).hep_job j j' =
        decide ((job_arrival j : Int) + task_priority_point (job_task (Task := Task) j) ≤
          (job_arrival j' : Int) + task_priority_point (job_task (Task := Task) j')) :=
  fun _ _ => rfl

/-- For two jobs of the same task, GEL compares arrival times. -/
theorem hep_job_arrival_gel [JobTask Job Task] [PriorityPoint Task] [Arrival : JobArrival Job] :
    ∀ j j' : Job, same_task (Task := Task) j j' = true →
      (GEL Job Task).hep_job j j' = decide (job_arrival j ≤ job_arrival j') := by
  intro j j' hsame
  have htask : job_task (Task := Task) j = job_task (Task := Task) j' := of_decide_eq_true hsame
  rw [hep_job_priority_point, htask]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega'

/-- A higher-or-equal-priority job arrives no later than this bound. -/
theorem hep_job_arrives_before [JobTask Job Task] [PriorityPoint Task] [Arrival : JobArrival Job] :
    ∀ j j' : Job, (GEL Job Task).hep_job j' j = true →
      decide ((job_arrival j' : Int) ≤
        (job_arrival j : Int) + task_priority_point (job_task (Task := Task) j) -
          task_priority_point (job_task (Task := Task) j')) = true := by
  intro j j' h
  rw [hep_job_priority_point] at h
  have h' := of_decide_eq_true h
  exact decide_eq_true (by omega')

/-- The bound above is nonnegative. -/
theorem hep_job_arrives_after_zero [JobTask Job Task] [PriorityPoint Task] [Arrival : JobArrival Job] :
    ∀ j j' : Job, (GEL Job Task).hep_job j' j = true →
      decide (0 ≤ (job_arrival j : Int) + task_priority_point (job_task (Task := Task) j) -
        task_priority_point (job_task (Task := Task) j')) = true := by
  intro j j' h
  have h' := of_decide_eq_true (hep_job_arrives_before j j' h)
  exact decide_eq_true (by omega')

/-- GEL respects sequential tasks. -/
theorem GEL_respects_sequential_tasks [JobTask Job Task] [PriorityPoint Task] [Arrival : JobArrival Job] :
    policy_respects_sequential_tasks (Task := Task) (GEL Job Task) := by
  intro j1 j2 hsame hle
  rw [hep_job_arrival_gel j1 j2 hsame]
  exact decide_eq_true hle

/-- In a schedule respecting GEL at preemption points, tasks are sequential. -/
theorem GEL_implies_sequential_tasks [JobTask Job Task] [PriorityPoint Task] [Arrival : JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ (sched : schedule PState) [JobReady0 : JobReady Job PState],
      @work_bearing_readiness Job _ _ _ PState JobReady0 arr_seq sched (GEL Job Task) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task) →
      sequential_tasks (Task := Task) arr_seq sched := by
  intro hva PState huni sched _ hwb hvs _ hvpm hresp j1 j2 t ha1 _ hsame hlt hs
  refine early_hep_job_is_scheduled arr_seq hva (GEL Job Task) GEL_is_transitive PState huni sched hwb hvs
    hvpm hresp j1 j2 ha1 hlt ?_ t hs
  refine (@always_higher_priority_jlfp Job _ (GEL Job Task) j1 j2).mpr ?_
  have hsame' : same_task (Task := Task) j2 j1 = true := by
    have : job_task (Task := Task) j1 = job_task (Task := Task) j2 := of_decide_eq_true hsame
    exact decide_eq_true this.symm
  rw [hep_job_arrival_gel j1 j2 hsame, hep_job_arrival_gel j2 j1 hsame']
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨Nat.le_of_lt hlt, Nat.not_le.mpr hlt⟩

end GELBasicFacts

end Prosa.Analysis.Facts.Priority.Gel
