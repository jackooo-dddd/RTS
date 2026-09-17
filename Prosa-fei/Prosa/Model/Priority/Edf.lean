-- Translated from: ../rt-proofs/model/priority/edf.v
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.Edf

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Priority.Classes

/-- EDF priority policy: jobs are ordered by their absolute deadlines. -/
instance EDF (Job : JobType) [JobDeadline Job] : JLFP_policy Job where
  hep_job := fun j1 j2 => Nat.ble (job_deadline j1) (job_deadline j2)

section PropertiesOfEDF

  variable {Job : JobType}
  variable [JobDeadline Job]

  variable (arr_seq : arrival_sequence Job)

  lemma EDF_is_reflexive :
      @reflexive_priorities Job (@JLFP_to_JLDP Job (EDF Job)) := by
    intro t j
    simp [hep_job_at, hep_job]

  lemma EDF_is_transitive :
      @transitive_priorities Job (@JLFP_to_JLDP Job (EDF Job)) := by
    intro t j1 j2 j3 h1 h2
    simp [hep_job_at, hep_job] at *
    exact Nat.le_trans h1 h2

  lemma EDF_is_total :
      @total_priorities Job (@JLFP_to_JLDP Job (EDF Job)) := by
    intro t j1 j2
    simp [hep_job_at, hep_job]
    exact Nat.le_total (job_deadline j1) (job_deadline j2)

end PropertiesOfEDF

end Prosa.Model.Priority.Edf
