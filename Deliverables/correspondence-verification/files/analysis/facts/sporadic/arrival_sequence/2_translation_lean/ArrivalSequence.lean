-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/sporadic/arrival_sequence.v

import Prosa.Analysis.Facts.Sporadic.ArrivalTimes

namespace Prosa.Analysis.Facts.Sporadic.ArrivalSequence

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Util.Notation
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.TaskArrivals
open Prosa.Analysis.Facts.JobIndex
open Prosa.Analysis.Facts.Sporadic.ArrivalTimes

/-! Representation notes: `size s` is `s.length`; `index x s` is
`List.idxOf x s`; `[:: x]` is `[x]`; `~ P` is `¬ P`; the Boolean
`valid_task_min_inter_arrival_time` hypothesis is `= true`; single
comparisons are Lean propositions. Binder orders and hypothesis sets follow
the elaborated types (unused section hypotheses are absent). -/

section SporadicArrivals

variable {Task : TaskType} [DecidableEq Task] [SporadicModel Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

/-- LEAN_HELPER: a list with at least two elements and no duplicates has two
distinct members. -/
private theorem two_distinct_of_length {α : Type _} (l : List α) (hnd : l.Nodup) (hl : 1 < l.length) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  match l, hnd, hl with
  | a :: b :: _, hnd, _ =>
    refine ⟨a, b, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    intro h; subst h
    exact (List.nodup_cons.mp hnd).1 List.mem_cons_self

/-- At most one job of a (valid) sporadic task arrives at any job's arrival time. -/
theorem size_task_arrivals_at_leq_one (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ¬ (∃ j : Job, 1 < (task_arrivals_at_job_arrival (Task := Task) arr_seq j).length ∧
          respects_sporadic_task_model arr_seq (job_task (Task := Task) j) ∧
          valid_task_min_inter_arrival_time (job_task (Task := Task) j) = true) := by
  rintro hva ⟨j, hsize, hspor, hvalid⟩
  have hnd : (task_arrivals_at_job_arrival (Task := Task) arr_seq j).Nodup := by
    unfold task_arrivals_at_job_arrival task_arrivals_at
    exact (hva.2 (job_arrival j)).filter _
  obtain ⟨a, b, ha, hb, hab⟩ := two_distinct_of_length _ hnd hsize
  unfold task_arrivals_at_job_arrival task_arrivals_at at ha hb
  rw [List.mem_filter] at ha hb
  have hta : job_task (Task := Task) a = job_task (Task := Task) j := of_decide_eq_true ha.2
  have htb : job_task (Task := Task) b = job_task (Task := Task) j := of_decide_eq_true hb.2
  have hra : job_arrival a = job_arrival j := hva.1 a _ (decide_eq_true ha.1)
  have hrb : job_arrival b = job_arrival j := hva.1 b _ (decide_eq_true hb.1)
  have hpos : 0 < task_min_inter_arrival_time (job_task (Task := Task) j) := of_decide_eq_true hvalid
  have := hspor a b hab ⟨_, decide_eq_true ha.1⟩ ⟨_, decide_eq_true hb.1⟩ hta htb (by rw [hra, hrb])
  rw [hra, hrb] at this
  try dsimp only [instant, duration] at *
  omega

variable (arr_seq : arrival_sequence Job)

/-- Only `j1` arrives among the jobs of its task at its arrival time. -/
theorem only_j_in_task_arrivals_at_j :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ j1 : Job, arrives_in arr_seq j1 → job_task (Task := Task) j1 = tsk →
            task_arrivals_at_job_arrival (Task := Task) arr_seq j1 = [j1] := by
  intro hva tsk hspor hvalid j1 h1 ht1
  have hmem : j1 ∈ task_arrivals_at_job_arrival (Task := Task) arr_seq j1 := by
    unfold task_arrivals_at_job_arrival task_arrivals_at
    rw [List.mem_filter]
    exact ⟨of_decide_eq_true (job_in_arrivals_at arr_seq hva.1 j1 (job_arrival j1) h1 rfl),
      by simp [job_of_task]⟩
  have hle : (task_arrivals_at_job_arrival (Task := Task) arr_seq j1).length ≤ 1 := by
    refine Nat.le_of_not_lt (fun hlt => size_task_arrivals_at_leq_one arr_seq hva ⟨j1, hlt, ?_, ?_⟩)
    · rw [ht1]; exact hspor
    · rw [ht1]; exact hvalid
  match hl : task_arrivals_at_job_arrival (Task := Task) arr_seq j1, hmem, hle with
  | [x], hm, _ => simp at hm; rw [hm]
  | [], hm, _ => simp at hm
  | _ :: _ :: _, _, hle' => simp at hle'

/-- Only `j1` arrives among the jobs of `tsk` at its arrival time. -/
theorem only_j_at_job_arrival_j :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ j1 : Job, arrives_in arr_seq j1 → job_task (Task := Task) j1 = tsk →
            ∀ t : instant, job_arrival j1 = t → task_arrivals_at arr_seq tsk t = [j1] := by
  intro hva tsk hspor hvalid j1 h1 ht1 t ht
  have := only_j_in_task_arrivals_at_j arr_seq hva tsk hspor hvalid j1 h1 ht1
  unfold task_arrivals_at_job_arrival at this
  rw [ht1, ht] at this
  exact this

/-- `j1` has index `0` among the task arrivals at its arrival time. -/
theorem index_j_in_task_arrivals_at :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ j1 : Job, arrives_in arr_seq j1 → job_task (Task := Task) j1 = tsk →
            (task_arrivals_at_job_arrival (Task := Task) arr_seq j1).idxOf j1 = 0 := by
  intro hva tsk hspor hvalid j1 h1 ht1
  rw [only_j_in_task_arrivals_at_j arr_seq hva tsk hspor hvalid j1 h1 ht1]
  simp

/-- The previous job arrives strictly earlier. -/
theorem prev_job_arr_lt :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ j1 : Job, arrives_in arr_seq j1 → job_task (Task := Task) j1 = tsk →
            0 < job_index (Task := Task) arr_seq j1 →
              job_arrival (prev_job (Task := Task) arr_seq j1) < job_arrival j1 := by
  intro hva tsk hspor hvalid j1 h1 ht1 hidx
  have hle := prev_job_arr_lte (Task := Task) arr_seq hva j1 h1 hidx
  refine Nat.lt_of_le_of_ne hle ?_
  apply uneq_job_uneq_arr arr_seq hva tsk hspor hvalid _ _
    (prev_job_arr (Task := Task) arr_seq j1 h1) h1
    (by rw [prev_job_task (Task := Task) arr_seq hva j1 h1 hidx, ht1]) ht1
  intro heq
  have := prev_job_index_j (Task := Task) arr_seq hva j1 h1 hidx hidx
  rw [heq] at this
  omega

omit [SporadicModel Task] in
/-- The task arrivals at `j1`'s arrival time are those in `[a, a + 1)`. -/
theorem task_arrivals_at_as_task_arrivals_between (tsk : Task) (j1 : Job) :
    job_task (Task := Task) j1 = tsk →
      task_arrivals_at_job_arrival (Task := Task) arr_seq j1 =
        task_arrivals_between arr_seq tsk (job_arrival j1) (job_arrival j1 + 1) := by
  intro ht1
  unfold task_arrivals_at_job_arrival task_arrivals_at task_arrivals_between arrivals_between bigCat
  rw [ht1]
  simp

/-- The task arrivals up to the previous job, followed by `j1`, are the task
arrivals up to `j1`. -/
theorem prev_job_cat :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ j1 : Job, arrives_in arr_seq j1 → job_task (Task := Task) j1 = tsk →
            0 < job_index (Task := Task) arr_seq j1 →
              task_arrivals_up_to_job_arrival (Task := Task) arr_seq (prev_job (Task := Task) arr_seq j1) ++ [j1] =
                task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1 := by
  intro hva tsk hspor hvalid j1 h1 ht1 hidx
  have hlt := prev_job_arr_lt arr_seq hva tsk hspor hvalid j1 h1 ht1 hidx
  have hpt := prev_job_task (Task := Task) arr_seq hva j1 h1 hidx
  rw [← only_j_in_task_arrivals_at_j arr_seq hva tsk hspor hvalid j1 h1 ht1,
    task_arrivals_at_as_task_arrivals_between arr_seq (job_task (Task := Task) j1) j1 rfl]
  unfold task_arrivals_up_to_job_arrival
  rw [hpt, task_arrivals_cat arr_seq (job_task (Task := Task) j1) (job_arrival (prev_job (Task := Task) arr_seq j1))
    (job_arrival j1) (Nat.le_of_lt hlt)]
  rw [task_arrivals_between_cat arr_seq (job_task (Task := Task) j1)
    (job_arrival (prev_job (Task := Task) arr_seq j1) + 1) (job_arrival j1) (job_arrival j1 + 1) hlt
    (Nat.le_succ _)]
  rw [no_jobs_between_consecutive_jobs (Task := Task) arr_seq hva j1 h1 hidx hidx]
  simp

end SporadicArrivals

end Prosa.Analysis.Facts.Sporadic.ArrivalSequence
