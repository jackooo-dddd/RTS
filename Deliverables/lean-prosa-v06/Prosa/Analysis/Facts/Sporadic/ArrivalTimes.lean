-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/sporadic/arrival_times.v

import Prosa.Model.Task.Arrival.Sporadic
import Prosa.Analysis.Facts.JobIndex

namespace Prosa.Analysis.Facts.Sporadic.ArrivalTimes

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Analysis.Facts.JobIndex

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-! Arrival times of jobs of a sporadic task. Binders follow the elaborated
source types; Booleans in `Prop` position are `= true`. -/

/-- A lower job index means a strictly earlier arrival. -/
theorem lower_index_implies_earlier_arrival {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
      valid_task_min_inter_arrival_time tsk = true →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = tsk → job_task (Task := Task) j2 = tsk →
        job_index (Task := Task) arr_seq j1 < job_index (Task := Task) arr_seq j2 →
        job_arrival j1 < job_arrival j2 := by
  intro hva tsk hsp hvalid j1 j2 h1 h2 ht1 ht2 hlt
  have hne : j1 ≠ j2 := by intro e; subst e; exact absurd hlt (Nat.lt_irrefl _)
  have hle : job_arrival j1 ≤ job_arrival j2 :=
    index_lte_implies_arrival_lte (Task := Task) arr_seq hva j2 j1 h2 h1 (by rw [ht1, ht2])
      (Nat.le_of_lt hlt)
  have hsep := hsp j1 j2 hne h1 h2 ht1 ht2 hle
  have hpos : 0 < task_min_inter_arrival_time tsk := of_decide_eq_true hvalid
  omega'

/-- Two jobs of the task are equal exactly when they arrive at the same time. -/
theorem same_jobs_iff_same_arr {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
      valid_task_min_inter_arrival_time tsk = true →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = tsk → job_task (Task := Task) j2 = tsk →
        (j1 = j2 ↔ job_arrival j1 = job_arrival j2) := by
  intro hva tsk hsp hvalid j1 j2 h1 h2 ht1 ht2
  constructor
  · intro e; rw [e]
  · intro heq
    by_contra hne
    have hidx : job_index (Task := Task) arr_seq j1 ≠ job_index (Task := Task) arr_seq j2 :=
      (diff_jobs_iff_diff_indices (Task := Task) arr_seq hva j1 j2 h1 h2 (by rw [ht1, ht2])).1 hne
    rcases Nat.lt_or_gt_of_ne hidx with hlt | hgt
    · have := lower_index_implies_earlier_arrival arr_seq hva tsk hsp hvalid j1 j2 h1 h2 ht1 ht2 hlt
      omega'
    · have := lower_index_implies_earlier_arrival arr_seq hva tsk hsp hvalid j2 j1 h2 h1 ht2 ht1 hgt
      omega'

/-- Distinct jobs of the task arrive at distinct times. -/
theorem uneq_job_uneq_arr {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
      valid_task_min_inter_arrival_time tsk = true →
      ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_task (Task := Task) j1 = tsk → job_task (Task := Task) j2 = tsk →
        j1 ≠ j2 → job_arrival j1 ≠ job_arrival j2 := by
  intro hva tsk hsp hvalid j1 j2 h1 h2 ht1 ht2 hne heq
  exact hne ((same_jobs_iff_same_arr arr_seq hva tsk hsp hvalid j1 j2 h1 h2 ht1 ht2).2 heq)

end Prosa.Analysis.Facts.Sporadic.ArrivalTimes
