-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/platform/nonpreemptive.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace FullyNonPreemptivePlatform

section FullyNonPreemptiveModel

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
  variable (H_nonpreemptive_sched : is_nonpreemptive_schedule job_cost sched)

  variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

  variable (H_job_cost_le_task_cost :
    cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)

  include H_nonpreemptive_sched H_completed_jobs_dont_execute H_job_cost_le_task_cost

  def can_be_preempted_for_fully_nonpreemptive_model (j : Job) (progr : Time) : Bool :=
    (progr == 0) || (progr == job_cost j)

  private def job_max_nps (j : Job) : Time := job_cost j

  private def task_max_nps (tsk : Task) : Time := task_cost tsk

  theorem fully_nonpreemptive_model_is_correct :
      correct_preemption_model arr_seq sched
        (can_be_preempted_for_fully_nonpreemptive_model job_cost) := by
    intro j _harr
    constructor
    · -- not_preemptive_implies_scheduled
      intro t hcant
      -- hcant : can_be_preempted ... = false means (service == 0 || service == job_cost j) = false
      -- so service ≠ 0 and service ≠ job_cost j, i.e. 0 < service and ¬completed_by
      unfold can_be_preempted_for_fully_nonpreemptive_model at hcant
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hcant
      have hpos : service sched j t > 0 := Nat.pos_of_ne_zero hcant.1
      have hncomp : ¬ completed_by job_cost sched j t := by
        intro hcomp
        exact hcant.2 (Nat.le_antisymm (H_completed_jobs_dont_execute j t) hcomp)
      -- From positive service, find an earlier time ft where j was scheduled
      obtain ⟨ft, hft_lt, hft_sched⟩ := scheduled_at_earlier_time sched j t hpos
      -- j was scheduled at ft, and j is not completed at t, so by nonpreemptive, j is scheduled at t
      exact H_nonpreemptive_sched j ft t (Nat.le_of_lt hft_lt) hft_sched hncomp
    · -- execution_starts_with_preemption_point
      intro prt hnsched hsched
      -- Need: can_be_preempted j (service sched j (prt+1)) = true
      -- We show service sched j (prt+1) = 0 by contradiction
      unfold can_be_preempted_for_fully_nonpreemptive_model
      simp only [Bool.or_eq_true_iff, beq_iff_eq]
      left
      by_contra hne
      have hpos : service sched j (prt + 1) > 0 := Nat.pos_of_ne_zero hne
      obtain ⟨ft, hft_lt, hft_sched⟩ := scheduled_at_earlier_time sched j (prt + 1) hpos
      -- ft < prt + 1, so ft ≤ prt
      have hft_le_prt : ft ≤ prt := Nat.lt_succ_iff.mp hft_lt
      have hncomp : ¬ completed_by job_cost sched j prt := by
        intro hcomp
        have hcomp' := completion_monotonic job_cost sched j prt (prt + 1) (Nat.le_succ prt) hcomp
        exact scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute (prt + 1) hsched hcomp'
      -- By nonpreemptive: j scheduled at ft, not completed at prt, ft ≤ prt ⇒ j scheduled at prt
      exact hnsched (H_nonpreemptive_sched j ft prt hft_le_prt hft_sched hncomp)

  theorem fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq
        (can_be_preempted_for_fully_nonpreemptive_model job_cost)
        (job_max_nps job_cost) (task_max_nps task_cost) := by
    intro j harr
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- can_be_preempted j 0 = true
      show can_be_preempted_for_fully_nonpreemptive_model job_cost j 0 = true
      unfold can_be_preempted_for_fully_nonpreemptive_model
      rfl
    · -- can_be_preempted j (job_cost j) = true
      show can_be_preempted_for_fully_nonpreemptive_model job_cost j (job_cost j) = true
      unfold can_be_preempted_for_fully_nonpreemptive_model
      simp only [Bool.or_eq_true, beq_iff_eq]
      exact Or.inr trivial
    · -- job_max_nps j ≤ task_max_nps (job_task j)
      intro _
      unfold job_max_nps task_max_nps
      exact H_job_cost_le_task_cost j harr
    · -- nonpreemptive_regions_have_bounded_length
      intro progr ⟨_, hle⟩
      by_cases hprogr : progr = 0
      · -- progr = 0: take pp = progr
        refine ⟨progr, le_refl _, ?_, ?_⟩
        · show progr ≤ progr + (job_max_nps job_cost j - Prosa.Util.Epsilon.ε)
          exact Nat.le_add_right _ _
        · unfold can_be_preempted_for_fully_nonpreemptive_model
          rw [hprogr]; rfl
      · -- progr > 0: take pp = job_cost j
        have hpos : 0 < progr := Nat.pos_of_ne_zero hprogr
        refine ⟨job_cost j, hle, ?_, ?_⟩
        · -- job_cost j ≤ progr + (job_max_nps job_cost j - ε)
          simp only [job_max_nps, Prosa.Util.Epsilon.ε]
          -- goal: job_cost j ≤ progr + (job_cost j - 1)
          -- When 0 < progr and progr ≤ job_cost j
          -- We have 1 ≤ job_cost j, so job_cost j - 1 + 1 = job_cost j
          -- Then job_cost j = job_cost j - 1 + 1 ≤ (job_cost j - 1) + progr ≤ progr + (job_cost j - 1)
          have hjpos : 1 ≤ job_cost j := Nat.one_le_iff_ne_zero.mpr (by intro h; rw [h] at hle; exact hprogr (Nat.le_zero.mp hle))
          calc job_cost j = job_cost j - 1 + 1 := (Nat.sub_add_cancel hjpos).symm
            _ ≤ job_cost j - 1 + progr := Nat.add_le_add_left hpos _
            _ = progr + (job_cost j - 1) := Nat.add_comm _ _
        · unfold can_be_preempted_for_fully_nonpreemptive_model
          simp only [Bool.or_eq_true, beq_iff_eq]
          exact Or.inr trivial

end FullyNonPreemptiveModel

end FullyNonPreemptivePlatform

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive
