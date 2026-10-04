-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/blocking_bound/edf.v

import Prosa.Analysis.Definitions.BlockingBound.Edf
import Prosa.Analysis.Facts.BusyInterval.Pi
import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Facts.Model.ArrivalCurves

namespace Prosa.Analysis.Facts.BlockingBound.Edf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Util.Minmax

/-! Under EDF scheduling, the maximum nonpreemptive segment of lower-priority
jobs is bounded by the EDF blocking bound.  Binders follow the elaborated source
type; the source's section-local `EDF` policy is the accepted `EDF` instance
over the accepted task-deadline-derived `job_deadline_from_task_deadline`,
passed explicitly.  Representation: a Boolean in `Prop` position is `= true`;
`x \in s` is `decide (x ∈ s) = true`. -/

section MaxNPSegmentIsBounded

variable {Job : JobType} [DecidableEq Job]

private theorem le_bigMaxListCond' {X : Type _} (xs : List X) (P : X → Bool) (F : X → Nat) (x : X)
    (hx : x ∈ xs) (hP : P x = true) : F x ≤ bigMaxListCond xs P F := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    unfold bigMaxListCond
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; rw [if_pos hP]; exact Nat.le_max_left _ _
    · have := ih h
      unfold bigMaxListCond at this
      split
      · exact Nat.le_trans this (Nat.le_max_right _ _)
      · exact this

private theorem bigMaxListCond_le {X : Type _} (xs : List X) (P : X → Bool) (F : X → Nat) (c : Nat)
    (h : ∀ x, x ∈ xs → P x = true → F x ≤ c) : bigMaxListCond xs P F ≤ c := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    have ih' := ih (fun x hx hP => h x (List.mem_cons_of_mem a hx) hP)
    unfold bigMaxListCond at ih' ⊢
    simp only [List.foldr_cons]
    split
    · exact Nat.max_le.2 ⟨h a List.mem_cons_self (by assumption), ih'⟩
    · exact ih'

/-- The maximum lower-priority nonpreemptive segment is bounded by the EDF
blocking bound. -/
theorem nonpreemptive_segments_bounded_by_blocking {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [TaskDeadline Task] [TaskMaxNonpreemptiveSegment Task]
    [JobTask Job Task] [JobCost Job] [JobArrival Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [JobPreemptable Job], valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → taskset_respects_max_arrivals arr_seq ts →
    ∀ j : Job, job_of_task tsk j = true →
    ∀ t1 t2 : instant,
      @busy_interval_prefix Job _ _ _ PState arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) j t1 t2 →
      @max_lp_nonpreemptive_segment Job _ _ arr_seq
          (@EDF Job _ (job_deadline_from_task_deadline Job Task)) _ j t1 ≤
        blocking_bound ts tsk (job_arrival j - t1) := by
  intro hva sched hcosts _ hvalid ts hts tsk _ hresp j hjt t1 t2 hbip
  have hjt' : job_task (Task := Task) j = tsk := by
    unfold job_of_task at hjt; exact of_decide_eq_true hjt
  have harr := hbip.2.2.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  refine Nat.le_trans (max_np_job_segment_bounded_by_max_np_task_segment (Task := Task) arr_seq sched
    (@EDF Job _ (job_deadline_from_task_deadline Job Task)) j t1 hvalid) ?_
  apply bigMaxListCond_le
  intro x hx hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  have hax := in_arrivals_implies_arrived arr_seq x 0 t1 (decide_eq_true hx)
  have hin : job_task (Task := Task) x ∈ ts := of_decide_eq_true (hts x hax)
  have hbx := in_arrivals_implies_arrived_between arr_seq hva.1 x 0 t1 (decide_eq_true hx)
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at hbx
  have hlp : ¬ (job_arrival x + task_deadline (job_task (Task := Task) x) ≤
      job_arrival j + task_deadline (job_task (Task := Task) j)) := by
    have h1 := hP.1
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact of_decide_eq_false h1
  have hvc := hcosts x hax
  unfold valid_job_cost at hvc
  simp only [decide_eq_true_eq] at hvc
  have hmax := non_pathological_max_arrivals (job_task (Task := Task) x) arr_seq
    (hresp _ (decide_eq_true hin)) x (by unfold job_of_task; exact decide_eq_true rfl) hax
  apply le_bigMaxListCond' ts _ (fun tsk_o => task_max_nonpreemptive_segment tsk_o - 1) _ hin
  rw [hjt'] at hlp
  simp only [blocking_relevant, Bool.and_eq_true, decide_eq_true_eq]
  have hc := hP.2
  have hc := hP.2
  refine ⟨⟨hmax, Nat.lt_of_lt_of_le hc hvc⟩, by omega'⟩

end MaxNPSegmentIsBounded

end Prosa.Analysis.Facts.BlockingBound.Edf
