-- Translated from: ../rt-proofs/analysis/facts/preemption/task/preemptive.v
import Prosa.Analysis.Definitions.Job_properties
import Prosa.Analysis.Facts.Preemption.Job.Preemptive
import Prosa.Model.Task.Preemption.Fully_preemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.Fully_preemptive
open Prosa.Model.Task.Concept
open Prosa.Analysis.Facts.Preemption.Job.Preemptive

section FullyPreemptiveModel

variable {Task : TaskType}
variable [TaskCost Task]
variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

lemma fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions :
    model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq := by
  intro j _
  constructor
  · -- job_respects_max_nonpreemptive_segment
    unfold job_respects_max_nonpreemptive_segment
    by_cases hcost : job_cost j = 0
    · rw [job_max_nps_is_0 j hcost]
      simp [task_max_nonpreemptive_segment, Prosa.Util.Epsilon.ε]
    · have hpos : job_cost j > 0 := Nat.pos_of_ne_zero hcost
      rw [job_max_nps_is_ε j hpos]
      simp [task_max_nonpreemptive_segment, Prosa.Util.Epsilon.ε]
  · -- nonpreemptive_regions_have_bounded_length
    intro ρ _
    exact ⟨ρ, le_refl ρ, Nat.le_add_right ρ _, by simp [job_preemptable]⟩

lemma fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched := by
  constructor
  · exact valid_fully_preemptive_model arr_seq sched
  · exact fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq

end FullyPreemptiveModel

end Prosa.Analysis.Facts.Preemption.Task.Preemptive
