-- Translated from: ../rt-proofs/analysis/facts/edf.v
import Prosa.Model.Priority.Edf
import Prosa.Model.Task.Absolute_deadline

namespace Prosa.Analysis.Facts.Edf

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Absolute_deadline
open Prosa.Model.Priority.Classes
open Prosa.Model.Priority.Edf

section PropertiesOfEDF

  variable {Task : TaskType}
  variable [TaskDeadline Task]
  variable [DecidableEq Task]

  variable {Job : JobType}
  variable [JobTask Job Task]
  variable [JobArrival Job]
  variable [JobCost Job]

  variable (arr_seq : arrival_sequence Job)

  lemma EDF_respects_sequential_tasks :
      @policy_respects_sequential_tasks Task Job
        inferInstance inferInstance
        (@EDF Job (job_deadline_from_task_deadline Job Task))
        inferInstance := by
    intro j1 j2 TSK ARR
    simp only [hep_job, job_deadline, Nat.ble_eq]
    rw [TSK]
    exact Nat.add_le_add_right ARR _

end PropertiesOfEDF

end Prosa.Analysis.Facts.Edf
