-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/offset.v

import Prosa.Model.Task.Offset
import Prosa.Analysis.Facts.JobIndex

namespace Prosa.Analysis.Facts.Model.Offset

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Offset
open Prosa.Analysis.Facts.JobIndex
open Prosa.Util.List

/-! Representation notes: a single comparison in `Prop` position is the Lean
proposition; `x \in s` is `decide (x ∈ s) = true`. Binder orders follow the
elaborated types (section hypotheses appear only in the statements that use
them). -/

/-- A job of `tsk` with index `0` arrives at the task offset. -/
theorem first_job_arrival {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (tsk : Task) (j : Job), job_task j = tsk → valid_offset arr_seq tsk →
        arrives_in arr_seq j → job_index (Task := Task) arr_seq j = 0 →
          job_arrival j = task_offset tsk := by
  intro hva tsk j htsk hvo harr hidx
  obtain ⟨BEFORE, j', ARR', TSK, ARRIVAL⟩ := hvo
  have hle : job_index (Task := Task) arr_seq j ≤ job_index (Task := Task) arr_seq j' := by
    rw [hidx]; exact Nat.zero_le _
  have h1 := index_lte_implies_arrival_lte arr_seq hva j' j ARR' harr (TSK.trans htsk.symm) hle
  have h2 := BEFORE j htsk
  rw [ARRIVAL] at h1
  exact Nat.le_antisymm h1 h2

/-- The offset of a task of `ts` is at most the maximum offset of `ts`. -/
theorem max_offset_g {Task : TaskType} [DecidableEq Task] [TaskOffset Task] (tsk : Task)
    (ts : TaskSet Task) :
    decide (tsk ∈ ts) = true → task_offset tsk ≤ max_task_offset ts := by
  intro h
  simp only [decide_eq_true_eq] at h
  exact in_max0_le _ _ (List.mem_map_of_mem h)

end Prosa.Analysis.Facts.Model.Offset
