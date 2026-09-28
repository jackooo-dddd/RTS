-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/blocking_bound/fp.v

import Prosa.Analysis.Definitions.BlockingBound.Fp
import Prosa.Analysis.Facts.BusyInterval.Pi

namespace Prosa.Analysis.Facts.BlockingBound.Fp

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Analysis.Definitions.BlockingBound.Fp
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Util.Minmax

/-! Under FP scheduling, the maximum nonpreemptive segment of lower-priority
jobs is bounded by the FP blocking bound.  Binders follow the elaborated source
type; the canonical FP-to-JLFP conversion of the source is the accepted
`FP_to_JLFP`, passed explicitly.  Representation: a Boolean in `Prop` position
is `= true`. -/

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

/-- The maximum lower-priority nonpreemptive segment is bounded by the FP
blocking bound. -/
theorem nonpreemptive_segments_bounded_by_blocking {Task : TaskType} [DecidableEq Task]
    [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task] [JobCost Job] {PState : ProcessorState Job}
    (FP : FP_policy Task) (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JobPreemptable Job] :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ (tsk : Task) (j : Job), job_of_task tsk j = true →
    ∀ t : instant,
      @max_lp_nonpreemptive_segment Job _ _ arr_seq (FP_to_JLFP FP) _ j t ≤ blocking_bound ts tsk := by
  intro hvalid ts hts tsk j hjt t
  have hjt' : job_task (Task := Task) j = tsk := by
    unfold job_of_task at hjt; exact of_decide_eq_true hjt
  refine Nat.le_trans (max_np_job_segment_bounded_by_max_np_task_segment (Task := Task) arr_seq sched
    (FP_to_JLFP FP) j t hvalid) ?_
  apply bigMaxListCond_le
  intro x hx hP
  simp only [Bool.and_eq_true] at hP
  have hin : job_task (Task := Task) x ∈ ts :=
    of_decide_eq_true (hts x (in_arrivals_implies_arrived arr_seq x 0 t (decide_eq_true hx)))
  apply le_bigMaxListCond' ts _ (fun tsk_other => task_max_nonpreemptive_segment tsk_other - 1) _ hin
  have h1 : (!FP.hep_task (job_task (Task := Task) x) (job_task (Task := Task) j)) = true := hP.1
  rw [hjt'] at h1
  exact h1

end MaxNPSegmentIsBounded

end Prosa.Analysis.Facts.BlockingBound.Fp
