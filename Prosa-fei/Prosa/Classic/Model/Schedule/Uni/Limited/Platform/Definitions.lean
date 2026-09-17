-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/platform/definitions.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Util.Epsilon
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Util.Epsilon

namespace LimitedPreemptionPlatform

section Properties

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  section PreemptionTime

    variable (can_be_preempted : Job → Time → Bool)

    def preemption_time (t : Time) : Bool :=
      match sched t with
      | some j => can_be_preempted j (service sched j t)
      | none => true

    section CorrectPreemptionModel

      def not_preemptive_implies_scheduled (j : Job) : Prop :=
        ∀ t,
          can_be_preempted j (service sched j t) = false →
          scheduled_at sched j t = true

      def execution_starts_with_preemption_point (j : Job) : Prop :=
        ∀ prt,
          ¬ (scheduled_at sched j prt = true) →
          scheduled_at sched j (prt + 1) = true →
          can_be_preempted j (service sched j (prt + 1)) = true

      def correct_preemption_model : Prop :=
        ∀ j,
          arrives_in arr_seq j →
          not_preemptive_implies_scheduled sched can_be_preempted j
          ∧ execution_starts_with_preemption_point sched can_be_preempted j

    end CorrectPreemptionModel

    section ModelWithBoundedNonpreemptiveRegions

      def job_cannot_become_nonpreemptive_before_execution (j : Job) : Prop :=
        can_be_preempted j 0 = true

      def job_cannot_be_nonpreemptive_after_completion (j : Job) : Prop :=
        can_be_preempted j (job_cost j) = true

      variable (job_max_nps : Job → Time)
      variable (task_max_nps : Task → Time)

      def job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (j : Job) : Prop :=
        arrives_in arr_seq j →
        job_max_nps j ≤ task_max_nps (job_task j)

      def nonpreemptive_regions_have_bounded_length (j : Job) : Prop :=
        ∀ progr,
          0 ≤ progr ∧ progr ≤ job_cost j →
          ∃ preemption_point,
            progr ≤ preemption_point ∧ preemption_point ≤ progr + (job_max_nps j - ε) ∧
            can_be_preempted j preemption_point = true

      def model_with_bounded_nonpreemptive_segments : Prop :=
        ∀ j,
          arrives_in arr_seq j →
          job_cannot_become_nonpreemptive_before_execution can_be_preempted j
          ∧ job_cannot_be_nonpreemptive_after_completion job_cost can_be_preempted j
          ∧ job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arr_seq job_max_nps task_max_nps j
          ∧ nonpreemptive_regions_have_bounded_length job_cost can_be_preempted job_max_nps j

    end ModelWithBoundedNonpreemptiveRegions

    section Lemmas

      variable (job_max_nps : Job → Time)
      variable (task_max_nps : Task → Time)

      variable (H_correct_preemption_model :
        ∀ j, arrives_in arr_seq j →
          not_preemptive_implies_scheduled sched can_be_preempted j
          ∧ execution_starts_with_preemption_point sched can_be_preempted j)
      variable (H_model_with_bounded_np_segments :
        ∀ j, arrives_in arr_seq j →
          job_cannot_become_nonpreemptive_before_execution can_be_preempted j
          ∧ job_cannot_be_nonpreemptive_after_completion job_cost can_be_preempted j
          ∧ job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arr_seq job_max_nps task_max_nps j
          ∧ nonpreemptive_regions_have_bounded_length job_cost can_be_preempted job_max_nps j)

      variable (H_jobs_come_from_arrival_sequence :
        jobs_come_from_arrival_sequence sched arr_seq)

      include H_correct_preemption_model H_model_with_bounded_np_segments H_jobs_come_from_arrival_sequence

      theorem zero_is_pt : preemption_time sched can_be_preempted 0 = true := by
        unfold preemption_time
        cases hsched : sched 0 with
        | none => rfl
        | some j =>
          simp only []
          have hsched_at : scheduled_at sched j 0 = true := by
            unfold scheduled_at; rw [hsched]; exact beq_self_eq_true (some j)
          have harr := H_jobs_come_from_arrival_sequence j 0 hsched_at
          have hserv : service sched j 0 = 0 := by
            unfold service service_during
            rw [Finset.Ico_self]; exact Finset.sum_empty
          rw [hserv]
          exact (H_model_with_bounded_np_segments j harr).1
      theorem first_moment_is_pt :
          ∀ j prt,
            arrives_in arr_seq j →
            ¬ (scheduled_at sched j prt = true) →
            scheduled_at sched j (prt + 1) = true →
            preemption_time sched can_be_preempted (prt + 1) = true := by
        intro j prt harr hnsched hsched
        unfold preemption_time
        have hsched_eq : sched (prt + 1) = some j := by
          simp [scheduled_at] at hsched; exact hsched
        rw [hsched_eq]
        exact (H_correct_preemption_model j harr).2 prt hnsched hsched
    end Lemmas

  end PreemptionTime

  section Execution

    def work_conserving := Platform.work_conserving job_arrival job_cost arr_seq sched

  end Execution

  section FP

    variable (preemption_model : Job → Time → Bool)

    variable (higher_eq_priority : FP_policy Task)

    def respects_FP_policy_at_preemption_point : Prop :=
      ∀ j j_hp t,
        preemption_time sched preemption_model t = true →
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority (job_task j_hp) (job_task j) = true

  end FP

  section JLFP

    variable (preemption_model : Job → Time → Bool)

    variable (higher_eq_priority : JLFP_policy Job)

    def respects_JLFP_policy_at_preemption_point : Prop :=
      ∀ j j_hp t,
        preemption_time sched preemption_model t = true →
        arrives_in arr_seq j →
        backlogged job_arrival job_cost sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority j_hp j = true

  end JLFP

end Properties

end LimitedPreemptionPlatform

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
