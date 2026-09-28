-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/pi_bound.v

import Prosa.Analysis.Facts.BusyInterval.Pi

namespace Prosa.Analysis.Facts.BusyInterval.PiBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.Uniprocessor
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Analysis.Facts.BusyInterval.Pi
open scoped BigOperators

/-! Priority inversion caused only by nonpreemptive segments is bounded by any
bound on the maximum lower-priority nonpreemptive segment.
Binders follow the elaborated source type (the unused task-cost context, work
conservation and reflexivity hypotheses are absent, as in the source).
Representation: a Boolean in `Prop` position is `= true`. -/

section PriorityInversionIsBounded

variable {Job : JobType} [DecidableEq Job]

/-- The cumulative priority inversion over an interval is at most its length. -/
private theorem cumulative_priority_inversion_le_length [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t1 t2 : instant) :
    cumulative_priority_inversion arr_seq sched j t1 t2 ≤ t2 - t1 := by
  unfold cumulative_priority_inversion
  calc ∑ t ∈ Finset.Ico t1 t2, (priority_inversion arr_seq sched j t).toNat
      ≤ ∑ t ∈ Finset.Ico t1 t2, 1 := Finset.sum_le_sum (fun t _ => Bool.toNat_le _)
    _ = t2 - t1 := by simp

/-- A bound on the maximum lower-priority nonpreemptive segment bounds the
priority inversion. -/
theorem priority_inversion_is_bounded {Task : TaskType} [DecidableEq Task]
    [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState) (JLFP : JLFP_policy Job),
      transitive_job_priorities JLFP →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched → valid_schedule sched arr_seq →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
      valid_preemption_model arr_seq sched →
    ∀ (tsk : Task) (blocking_bound : duration → duration),
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
      (∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
        busy_interval_prefix arr_seq sched j t1 t2 →
        max_lp_nonpreemptive_segment arr_seq j t1 ≤ blocking_bound (job_arrival j - t1)) →
      priority_inversion_is_bounded_by arr_seq sched tsk blocking_bound := by
  intro hva PState sched JLFP htrans hvalid _ hwb hvs hresp hvpm tsk B huni hunit hideal hbound
  intro j ha hjt hpos t1 t2 hbip
  have harr := hbip.2.2.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  have hlen := cumulative_priority_inversion_le_length arr_seq sched j t1 t2
  by_cases hshort : t2 - t1 ≤ B (job_arrival j - t1)
  · exact Nat.le_trans hlen hshort
  · obtain ⟨ppt, hppt, hin⟩ := preemption_time_exists (Task := Task) arr_seq hva huni sched JLFP htrans
      hvpm hwb hvs hresp j ha (decide_eq_true hpos) t1 t2 hbip hvalid hunit hideal
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    have h1 := priority_inversion_occurs_only_till_preemption_point arr_seq hva huni sched JLFP htrans hvpm
      hwb hvs hresp j ha (decide_eq_true hpos) t1 t2 hbip ppt hppt hin.1
    have h2 := cumulative_priority_inversion_le_length arr_seq sched j t1 ppt
    have h3 := hbound j t1 t2 ha hjt hbip
    omega'

end PriorityInversionIsBounded

end Prosa.Analysis.Facts.BusyInterval.PiBound
