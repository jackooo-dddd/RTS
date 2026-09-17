-- Translated from: ../rt-proofs/analysis/facts/model/workload.v
import Prosa.Model.Aggregate.Workload
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.Model.Workload

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Facts.Behavior.Arrivals

section WorkloadFacts

  variable {Task : TaskType}
  variable [TaskCost Task]
  variable {Job : JobType}
  variable [JobTask Job Task]
  variable [JobArrival Job]
  variable [JobCost Job]

  variable (arr_seq : arrival_sequence Job)

  theorem workload_of_jobs_cat :
      ∀ t t1 t2 (P : Job → Bool),
        t1 ≤ t ∧ t ≤ t2 →
        workload_of_jobs P (arrivals_between arr_seq t1 t2) =
        workload_of_jobs P (arrivals_between arr_seq t1 t)
        + workload_of_jobs P (arrivals_between arr_seq t t2) := by
    intro t t1 t2 P ⟨hle1, hle2⟩
    have hcat := arrivals_between_cat arr_seq t1 t t2 hle1 hle2
    rw [workload_of_jobs, workload_of_jobs, workload_of_jobs,
        hcat, List.filter_append, List.map_append, List.sum_append]

end WorkloadFacts

end Prosa.Analysis.Facts.Model.Workload
