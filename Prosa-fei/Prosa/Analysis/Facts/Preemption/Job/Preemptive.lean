-- Translated from: ../rt-proofs/analysis/facts/preemption/job/preemptive.v
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Preemption.Fully_preemptive

namespace Prosa.Analysis.Facts.Preemption.Job.Preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.Fully_preemptive
open Prosa.Util.Epsilon
open Prosa.Util.List

section FullyPreemptiveModel

variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

lemma valid_fully_preemptive_model :
    valid_preemption_model arr_seq sched := by
  intro j _
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- job_cannot_become_nonpreemptive_before_execution
    unfold job_cannot_become_nonpreemptive_before_execution
    simp [job_preemptable, fully_preemptive_model]
  · -- job_cannot_be_nonpreemptive_after_completion
    unfold job_cannot_be_nonpreemptive_after_completion
    simp [job_preemptable, fully_preemptive_model]
  · -- not_preemptive_implies_scheduled
    unfold not_preemptive_implies_scheduled
    intro t h
    simp [job_preemptable, fully_preemptive_model] at h
  · -- execution_starts_with_preemption_point
    unfold execution_starts_with_preemption_point
    intro prt _ _
    simp [job_preemptable, fully_preemptive_model]

lemma job_max_nps_is_0 :
    ∀ j : Job,
      job_cost j = 0 →
      job_max_nonpreemptive_segment j = 0 := by
  intro j hcost
  unfold job_max_nonpreemptive_segment lengths_of_segments job_preemption_points
  simp [hcost, range, job_preemptable, fully_preemptive_model, distances, max0]

lemma job_max_nps_is_ε :
    ∀ j : Job,
      job_cost j > 0 →
      job_max_nonpreemptive_segment j = ε := by
  intro j hpos
  unfold job_max_nonpreemptive_segment lengths_of_segments job_preemption_points
  simp only [job_preemptable, fully_preemptive_model]
  have hfilter : List.filter (fun ρ => true) (range 0 (job_cost j)) = range 0 (job_cost j) := by
    simp
  rw [hfilter]
  unfold range
  simp only [Nat.sub_zero]
  set n := job_cost j with hn_def
  suffices hdist : distances (List.range' 0 (n + 1)) = List.replicate n 1 by
    rw [hdist]; unfold ε
    apply max0_of_uniform_set 1
    · simp; exact hpos
    · intro x hx; exact List.eq_of_mem_replicate hx
  unfold distances
  apply List.ext_getElem
  · rw [List.length_map, List.length_zip, List.length_drop, List.length_range',
        List.length_replicate]
    simp
  · intro i h1 h2
    rw [List.length_map, List.length_zip, List.length_drop, List.length_range'] at h1
    rw [List.getElem_map, List.getElem_zip, List.getElem_replicate]
    simp only [List.getElem_range', List.getElem_drop]
    omega

end FullyPreemptiveModel

end Prosa.Analysis.Facts.Preemption.Job.Preemptive
