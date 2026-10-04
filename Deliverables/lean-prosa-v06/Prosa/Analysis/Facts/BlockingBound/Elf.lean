-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/blocking_bound/elf.v

import Prosa.Analysis.Definitions.BlockingBound.Elf
import Prosa.Analysis.Facts.BusyInterval.Pi
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Facts.Model.ArrivalCurves
import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Analysis.Facts.Priority.Elf

namespace Prosa.Analysis.Facts.BlockingBound.Elf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Elf
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.BlockingBound.Elf
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Priority.Gel
open Prosa.Util.Minmax

/-! The ELF blocking bound bounds the lower-priority nonpreemptive segments.

Binders follow the elaborated source type: the section inputs and hypotheses
the lemma uses, in their elaborated order (of the three FP-policy hypotheses
only totality is used); instance inputs quantified after a hypothesis are
`∀ [..]` binders at that position. The source's exported `ELF FP` instance is
the accepted reducible definition, passed explicitly as the JLFP policy.
Representation: a Boolean in `Prop` position is `= true`; `x \in s` is
`decide (x ∈ s) = true`. -/

section MaxNPSegmentIsBounded

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The maximum nonpreemptive segment of lower-priority jobs arrived so far
is bounded by the ELF blocking bound. -/
theorem nonpreemptive_segments_bounded_by_blocking [TaskCost Task] [MaxArrivals Task]
    [TaskMaxNonpreemptiveSegment Task] [PriorityPoint Task] [JobTask Job Task] [JobCost Job]
    [JobArrival Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [JobPreemptable Job], valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
    ∀ ts : TaskSet Task, all_jobs_from_taskset arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → taskset_respects_max_arrivals arr_seq ts →
    ∀ j : Job, job_of_task tsk j = true →
    ∀ FP : FP_policy Task, total_task_priorities FP →
    ∀ t1 t2 : instant,
      @busy_interval_prefix Job _ _ _ PState arr_seq sched (ELF (Job := Job) FP) j t1 t2 →
      @max_lp_nonpreemptive_segment Job _ _ arr_seq (ELF (Job := Job) FP) _ j t1 ≤
        blocking_bound (FP := FP) ts tsk (job_arrival j - t1) := by
  intro hva sched hvjc _ hvm ts hall tsk _ hresp j hjt FP htot t1 t2 hbusy
  have hjt' : job_task (Task := Task) j = tsk := of_decide_eq_true hjt
  have hJa : t1 ≤ job_arrival j := by
    have h := hbusy.2.2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  refine Nat.le_trans (max_np_job_segment_bounded_by_max_np_task_segment (Task := Task) arr_seq sched
    (ELF (Job := Job) FP) j t1 hvm) ?_
  unfold blocking_bound
  apply (bigmax_leq_seqP _ _ _ _).mpr
  intro j' hj' hP
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hP
  obtain ⟨hnhep, hcostpos⟩ := hP
  have hcostpos' : 0 < job_cost j' := of_decide_eq_true hcostpos
  have harr' : arrives_in arr_seq j' := in_arrivals_implies_arrived arr_seq j' 0 t1 (decide_eq_true hj')
  have hin' : decide (job_task (Task := Task) j' ∈ ts) = true := hall j' harr'
  have hbtw := in_arrivals_implies_arrived_between arr_seq hva.1 j' 0 t1 (decide_eq_true hj')
  unfold arrived_between at hbtw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbtw
  refine leq_bigmax_cond_seq (fun tsk_o => task_max_nonpreemptive_segment tsk_o - 1) _ ts
    (job_task (Task := Task) j') (of_decide_eq_true hin') ?_
  -- the task of `j'` is blocking-relevant
  have hma : 0 < max_arrivals (job_task (Task := Task) j') 1 :=
    non_pathological_max_arrivals (job_task (Task := Task) j') arr_seq (hresp _ hin') j'
      (decide_eq_true rfl) harr'
  have htc : 0 < task_cost (job_task (Task := Task) j') := by
    have hv := hvjc j' harr'
    unfold valid_job_cost at hv
    exact Nat.lt_of_lt_of_le hcostpos' (of_decide_eq_true hv)
  have hrel : (decide (0 < max_arrivals (job_task (Task := Task) j') 1) &&
      decide (0 < task_cost (job_task (Task := Task) j'))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hma, htc⟩
  -- the priority of `j'` w.r.t. `j`
  change (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job j' j)) = false at hnhep
  rw [hjt'] at hnhep
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hnhep
  obtain ⟨hnhp, hcase⟩ := hnhep
  cases hh : FP.hep_task (job_task (Task := Task) j') tsk with
  | false =>
    have hhp : hp_task (FP := FP) tsk (job_task (Task := Task) j') = true := by
      rw [← not_hep_hp_task FP htot, hh]; rfl
    simp only [hhp, hrel, Bool.true_and, Bool.true_or]
  | true =>
    have hrev : FP.hep_task tsk (job_task (Task := Task) j') = true := by
      rw [← not_hp_hep_task FP htot, hnhp]; rfl
    have hgel : (GEL Job Task).hep_job j' j = false := by
      rcases hcase with h | h
      · rw [hh] at h; exact absurd h (by decide)
      · exact h
    rw [hep_job_priority_point] at hgel
    have hlt := of_decide_eq_false hgel
    rw [hjt'] at hlt
    have hep : ep_task (FP := FP) tsk (job_task (Task := Task) j') = true := by
      simp [ep_task, hh, hrev]
    have hpt : decide (((job_arrival j - t1 : Nat) : Int) + task_priority_point tsk <
        task_priority_point (job_task (Task := Task) j')) = true := by
      apply decide_eq_true
      have hsub : ((job_arrival j - t1 : Nat) : Int) = (job_arrival j : Int) - (t1 : Int) := by
        push_cast [Nat.cast_sub hJa]; ring
      rw [hsub]
      have h1 : (job_arrival j' : Int) < (t1 : Int) := by exact_mod_cast hbtw.2
      omega
    simp only [hep, hpt, hrel, Bool.and_self, Bool.or_true]

end MaxNPSegmentIsBounded

end Prosa.Analysis.Facts.BlockingBound.Elf
