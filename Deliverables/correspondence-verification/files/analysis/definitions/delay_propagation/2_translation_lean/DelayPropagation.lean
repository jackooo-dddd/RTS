-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/delay_propagation.v

import Prosa.Model.Task.Arrival.Curves
import Prosa.Model.Task.Jitter

namespace Prosa.Analysis.Definitions.DelayPropagation

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Readiness.Jitter
open Prosa.Model.Task.Jitter

/-! ## Arrival-curve propagation

The source's section `Let`s (`consistent_task_job_mapping`,
`bounded_arrival_delay`, `consistent_job_mapping`, `valid_arrival_delay`,
`valid_job_arrival_def`) are inlined.  The two `JobArrival` instances are
explicit arguments, as in the source. -/

/-- A delay-propagation mapping is structurally consistent and bounds the
arrival delay of every job of a task in `ts`. -/
def valid_delay_propagation_mapping {Task1 Task2 : TaskType}
    [DecidableEq Task1] [DecidableEq Task2]
    {Job1 Job2 : JobType} [DecidableEq Job1] [DecidableEq Job2]
    [JobTask Job1 Task1] [JobTask Job2 Task2]
    (ja1 : JobArrival Job1) (ja2 : JobArrival Job2)
    (job1_of : Job2 → Job1) (task1_of : Task2 → Task1)
    (delay_bound : Task2 → duration) (ts : List Task2) : Prop :=
  (∀ j2 : Job2, job_task (job1_of j2) = task1_of (job_task j2)) ∧
  (∀ j2 : Job2, decide (job_task j2 ∈ ts) = true →
    ja2.job_arrival j2 ≤ ja1.job_arrival (job1_of j2) + delay_bound (job_task j2))

/-- The arrival sequence of jobs of the second kind derived from `arr_seq1`. -/
def propagated_arrival_sequence {Job1 Job2 : JobType}
    [DecidableEq Job1] [DecidableEq Job2]
    (ja1 : JobArrival Job1) (job1_of : Job2 → Job1)
    (arr_seq1 : arrival_sequence Job1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (t : instant) : List Job2 :=
  (((arrivals_up_to arr_seq1 t).map job2_of).flatten).filter
    (fun j2 => decide (ja1.job_arrival (job1_of j2) + arrival_delay j2 = t))

/-- The inverse job mapping yields duplicate-free lists for arriving jobs. -/
def job_mapping_uniq {Job1 Job2 : JobType} [DecidableEq Job1] [DecidableEq Job2]
    (arr_seq1 : arrival_sequence Job1) (job2_of : Job1 → List Job2) : Prop :=
  ∀ j1 : Job1, arrives_in arr_seq1 j1 → (job2_of j1).Nodup

/-- The derived arrival sequence is valid for `ts` (the source's four-way
conjunction `[/\ _, _, _ & _]`). -/
def valid_arr_seq_propagation_mapping {Task2 : TaskType} [DecidableEq Task2]
    {Job1 Job2 : JobType} [DecidableEq Job1] [DecidableEq Job2]
    [JobTask Job2 Task2]
    (ja1 : JobArrival Job1) (ja2 : JobArrival Job2)
    (job1_of : Job2 → Job1) (delay_bound : Task2 → duration)
    (arr_seq1 : arrival_sequence Job1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (ts : List Task2) : Prop :=
  (∀ (j1 : Job1) (j2 : Job2), decide (j2 ∈ job2_of j1) = true ↔ job1_of j2 = j1) ∧
  job_mapping_uniq arr_seq1 job2_of ∧
  (∀ j2 : Job2, decide (job_task j2 ∈ ts) = true →
    arrives_in arr_seq1 (job1_of j2) → arrival_delay j2 ≤ delay_bound (job_task j2)) ∧
  (∀ j2 : Job2, ja2.job_arrival j2 = ja1.job_arrival (job1_of j2) + arrival_delay j2)

/-! ## Release-jitter propagation

The source's local instance `release_as_arrival` (release time
`job_arrival j + job_jitter j`) is written inline as
`⟨fun j => original_arrival.job_arrival j + job_jitter j⟩`. -/

theorem jitter_delay_mapping_valid {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (original_arrival : JobArrival Job) [TaskJitter Task] [JobJitter Job] :
    ∀ ts : TaskSet Task,
      valid_jitter_bounds (Job := Job) ts →
      valid_delay_propagation_mapping original_arrival
        ⟨fun j => original_arrival.job_arrival j + job_jitter j⟩
        id id task_jitter ts := by
  intro ts hvalid
  refine ⟨fun _ => rfl, ?_⟩
  intro j2 hin
  exact Nat.add_le_add_left (hvalid (job_task j2) hin j2 rfl) _

/-- The induced release sequence. -/
def release_sequence {Job : JobType} [DecidableEq Job]
    (original_arrival : JobArrival Job) [JobJitter Job]
    (arr_seq : arrival_sequence Job) : instant → List Job :=
  propagated_arrival_sequence original_arrival id arr_seq (fun j => [j]) job_jitter

theorem jitter_arr_seq_mapping_valid {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (original_arrival : JobArrival Job) [TaskJitter Task] [JobJitter Job] :
    ∀ (ts : TaskSet Task) (arr_seq : arrival_sequence Job),
      valid_jitter_bounds (Job := Job) ts →
      valid_arr_seq_propagation_mapping original_arrival
        ⟨fun j => original_arrival.job_arrival j + job_jitter j⟩
        id task_jitter arr_seq (fun j => [j]) job_jitter ts := by
  intro ts arr_seq hvalid
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · intro j1 j2
    simp only [List.mem_singleton, decide_eq_true_eq, id]
  · intro j1 _
    exact List.nodup_singleton j1
  · intro j2 hin _
    exact hvalid (job_task j2) hin j2 rfl

end Prosa.Analysis.Definitions.DelayPropagation
