-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/platform/preemptive.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Util.Epsilon
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Util.Epsilon

namespace FullyPreemptivePlatform

section FullyPreemptiveModel

  variable {Task : Type _} [DecidableEq Task]

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  def can_be_preempted_for_fully_preemptive_model (j : Job) (progr : Time) : Bool := true

  private def job_max_nps (j : Job) : Time := ε

  private def task_max_nps (tsk : Task) : Time := ε

  theorem fully_preemptive_model_is_correct :
    correct_preemption_model arr_seq sched can_be_preempted_for_fully_preemptive_model := by
    intro j _harr
    constructor
    · -- not_preemptive_implies_scheduled: can_be_preempted is always true, so hypothesis true=false is absurd
      intro t hcontr
      unfold can_be_preempted_for_fully_preemptive_model at hcontr
      exact absurd hcontr (by decide)
    · -- execution_starts_with_preemption_point: conclusion is can_be_preempted ... = true, which is trivially true
      intro prt _hnsched _hsched
      rfl

  theorem fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions :
    model_with_bounded_nonpreemptive_segments
      job_cost job_task arr_seq can_be_preempted_for_fully_preemptive_model
      (job_max_nps) (task_max_nps) := by
    intro j _harr
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- job_cannot_become_nonpreemptive_before_execution
      show can_be_preempted_for_fully_preemptive_model j 0 = true
      rfl
    · -- job_cannot_be_nonpreemptive_after_completion
      show can_be_preempted_for_fully_preemptive_model j (job_cost j) = true
      rfl
    · -- job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment
      intro _
      exact le_refl _
    · -- nonpreemptive_regions_have_bounded_length
      intro progr _hprogr
      refine ⟨progr, le_refl progr, ?_, rfl⟩
      -- job_max_nps j = ε, so job_max_nps j - ε = 0
      have h : job_max_nps j = ε := rfl
      rw [h, Nat.sub_self, Nat.add_zero]

end FullyPreemptiveModel

end FullyPreemptivePlatform

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive
