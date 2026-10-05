-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/facts/job_constructor.v

import Prosa.Implementation.Definitions.JobConstructor
import Prosa.Util.Bigcat

namespace Prosa.Implementation.Facts.JobConstructor

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Time
open Prosa.Util.Notation
open Prosa.Util.Bigcat
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Definitions.MaximalArrivalSequence
open Prosa.Implementation.Definitions.JobConstructor

/-! Facts about the job-constructor function used with the concrete arrival sequence.

Binders follow the elaborated source types: the section's `ts` and `H_ts_uniq` appear only in the statements that
use them; the local `ConcreteMaxArrivals` is the accepted global instance; the section-local `arr_seq` is inlined.
Representation: `uniq s` is `s.Nodup`; `x \in s` is `decide (x ∈ s) = true`; `size` is `List.length`; the record
projections `task.job_task` etc. are the structure projections `concrete_job.job_task` etc. -/

/-- LEAN_HELPER: membership in the generated jobs. -/
private theorem mem_generate_jobs_at {tsk : concrete_task} {n : Nat} {t : instant} {j : Job} :
    j ∈ generate_jobs_at tsk n t ↔ ∃ i, i ∈ List.range' 0 n ∧ generate_job_at tsk t i = j := by
  simp only [generate_jobs_at, List.mem_map]

/-- `generate_jobs_at tsk n t` generates `n` jobs. -/
theorem job_generation_valid_number (ts : List Task) (tsk : Task) (n : Nat) (t : instant) :
    decide (tsk ∈ ts) = true → (generate_jobs_at tsk n t).length = n := by
  intro _
  simp [generate_jobs_at]

/-- The generated jobs are pairwise distinct. -/
theorem generate_jobs_at_unique (tsk : concrete_task) (n : Nat) (t : instant) :
    (generate_jobs_at tsk n t).Nodup := by
  unfold generate_jobs_at
  refine List.Nodup.map ?_ List.nodup_range'
  intro a b h
  have := congrArg concrete_job.job_id h
  simpa [generate_job_at] using this

/-- The arrival time of a job is consistent with its position in the concrete arrival sequence. -/
theorem job_arrival_consistent (ts : List Task) (j : Job) (t : instant) :
    decide (j ∈ arrivals_at (concrete_arrival_sequence generate_jobs_at ts) t) = true →
      concrete_job.job_arrival j = t := by
  intro h
  simp only [decide_eq_true_eq, arrivals_at, concrete_arrival_sequence, bigCatSeqAll,
    List.mem_flatMap] at h
  obtain ⟨tsk, _, hj⟩ := h
  obtain ⟨i, _, rfl⟩ := mem_generate_jobs_at.mp hj
  rfl

/-- The arrivals at any instant are pairwise distinct. -/
theorem arrivals_at_unique (ts : List Task) :
    ts.Nodup → ∀ t : instant, (arrivals_at (concrete_arrival_sequence generate_jobs_at ts) t).Nodup := by
  intro hts t
  simp only [arrivals_at, concrete_arrival_sequence, bigCatSeqAll]
  rw [List.nodup_flatMap]
  refine ⟨fun tsk _ => generate_jobs_at_unique _ _ _, ?_⟩
  refine hts.pairwise_of_forall_ne ?_
  intro tsk1 _ tsk2 _ hne j hj1 hj2
  obtain ⟨i1, _, rfl⟩ := mem_generate_jobs_at.mp hj1
  obtain ⟨i2, _, h2⟩ := mem_generate_jobs_at.mp hj2
  exact hne (congrArg concrete_job.job_task h2).symm

/-- The arrivals in any interval are pairwise distinct. -/
theorem arrivals_between_unique (ts : List Task) :
    ts.Nodup → ∀ t1 t2 : instant,
      (arrivals_between (concrete_arrival_sequence generate_jobs_at ts) t1 t2).Nodup := by
  intro hts t1 t2
  unfold arrivals_between
  refine bigcat_nat_uniq _ (arrivals_at_unique ts hts) ?_ t1 t2
  intro j i1 i2 h1 h2
  rw [← job_arrival_consistent ts j i1 (decide_eq_true h1),
    ← job_arrival_consistent ts j i2 (decide_eq_true h2)]

/-- The generated jobs are jobs of `tsk` arriving at `t` whose cost is at most the task cost. -/
theorem job_generation_valid_jobs (tsk : concrete_task) (n : Nat) (t : instant) (j : Job) :
    decide (j ∈ generate_jobs_at tsk n t) = true →
      concrete_job.job_task j = tsk ∧ concrete_job.job_arrival j = t ∧
        concrete_job.job_cost j ≤ concrete_task.task_cost tsk := by
  intro h
  obtain ⟨i, _, rfl⟩ := mem_generate_jobs_at.mp (of_decide_eq_true h)
  exact ⟨rfl, rfl, Nat.le_refl _⟩

end Prosa.Implementation.Facts.JobConstructor
