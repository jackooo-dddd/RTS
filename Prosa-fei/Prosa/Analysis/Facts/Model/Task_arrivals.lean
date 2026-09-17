-- Translated from: ../rt-proofs/analysis/facts/model/task_arrivals.v
import Prosa.Model.Task.Arrivals

namespace Prosa.Analysis.Facts.Model.Task_arrivals

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

section TaskArrivals

variable {Job : JobType}
variable {Task : TaskType}
variable [DecidableEq Task]
variable [JobTask Job Task]

variable (arr_seq : arrival_sequence Job)

variable (tsk : Task)

theorem num_arrivals_of_task_cat :
    ∀ (t t1 t2 : instant),
      t1 ≤ t ∧ t ≤ t2 →
      number_of_task_arrivals arr_seq tsk t1 t2 =
      number_of_task_arrivals arr_seq tsk t1 t + number_of_task_arrivals arr_seq tsk t t2 := by
  intro t t1 t2 ⟨h1, h2⟩
  simp only [number_of_task_arrivals, task_arrivals_between, arrivals_between, arrivals_at,
    Prosa.Util.Notation.bigCat]
  have heq : t2 - t1 = (t - t1) + (t2 - t) := by
    simp only [instant] at *; omega
  have hmap : ∀ i, arr_seq (t1 + (t - t1 + i)) = arr_seq (t + i) := by
    intro i; congr 1; simp only [instant] at *; omega
  rw [heq, List.range_add, List.map_append, List.flatten_append, List.filter_append,
    List.length_append]
  congr 1
  have : List.map (fun i => arr_seq (t1 + i)) (List.map (fun x => t - t1 + x) (List.range (t2 - t))) =
         List.map (fun i => arr_seq (t + i)) (List.range (t2 - t)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hmap i
  rw [this]

end TaskArrivals

end Prosa.Analysis.Facts.Model.Task_arrivals
