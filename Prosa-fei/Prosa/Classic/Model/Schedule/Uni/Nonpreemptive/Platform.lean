-- Translated from: classic/model/schedule/uni/nonpreemptive/platform.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Platform

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority

namespace NonpreemptivePlatform

section Properties

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  private abbrev job_completed_by := completed_by job_cost sched
  private abbrev job_scheduled_at := scheduled_at sched

  section PreemptionPoint

    def is_preemption_point' (t : Time) : Prop :=
      t = 0
      ∨ sched (t - 1) = none
      ∨ ∃ j, scheduled_at sched j (t - 1) = true ∧ completed_by job_cost sched j t

    def is_preemption_point (t : Time) : Prop :=
      t = 0 ∨ ∀ j, scheduled_at sched j (t - 1) = true → completed_by job_cost sched j t

    theorem defitions_of_preemption_point_are_equal :
        ∀ t, is_preemption_point job_cost sched t ↔ is_preemption_point' job_cost sched t := by
      intro t
      unfold is_preemption_point is_preemption_point'
      constructor
      · rintro (rfl | h)
        · left; rfl
        · right
          cases hsched : sched (t - 1) with
          | none => left; rfl
          | some s =>
            right
            have hsa : scheduled_at sched s (t - 1) = true := by
              unfold scheduled_at; rw [hsched]; exact beq_self_eq_true s
            exact ⟨s, hsa, h s hsa⟩
      · rintro (rfl | h | ⟨j', hj1, hj2⟩)
        · left; rfl
        · right
          intro j hsched
          exfalso
          have h1 : sched (t - 1) = some j := eq_of_beq hsched
          exact absurd h1 (by rw [h]; exact fun h2 => nomatch h2)
        · right
          intro j hsched
          have heq : j = j' := only_one_job_scheduled sched j j' (t - 1) hsched hj1
          rw [heq]; exact hj2

  end PreemptionPoint

  section Execution

    def work_conserving :=
      Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving job_arrival job_cost arr_seq sched

  end Execution

  section FP

    variable (higher_eq_priority : FP_policy sporadic_task)

    def respects_FP_policy_at_preemption_point :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        is_preemption_point job_cost sched t →
        higher_eq_priority (job_task j_hp) (job_task j) = true

  end FP

  section JLFP

    variable (higher_eq_priority : JLFP_policy Job)

    def respects_JLFP_policy_at_preemption_point :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        is_preemption_point job_cost sched t →
        higher_eq_priority j_hp j = true

  end JLFP

end Properties

end NonpreemptivePlatform

end Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Platform
