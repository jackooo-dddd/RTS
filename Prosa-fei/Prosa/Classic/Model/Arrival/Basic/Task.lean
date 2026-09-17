-- Translated from: ../rt-proofs/classic/model/arrival/basic/task.v
import Prosa.Classic.Model.Time
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Prosa.Classic.Model.Arrival.Basic.Task

open Prosa.Classic.Model.Time

namespace SporadicTask

  section BasicTask
    variable {Task : Type _} [DecidableEq Task]
    variable (task_cost : Task → Time)
    variable (task_period : Task → Time)
    variable (task_deadline : Task → Time)

    section ValidParameters
      variable (tsk : Task)

      def task_cost_positive := task_cost tsk > 0
      def task_period_positive := task_period tsk > 0
      def task_deadline_positive := task_deadline tsk > 0

      def task_cost_le_deadline := task_cost tsk ≤ task_deadline tsk
      def task_cost_le_period := task_cost tsk ≤ task_period tsk

      def is_valid_sporadic_task :=
        task_cost_positive task_cost tsk ∧
        task_period_positive task_period tsk ∧
        task_deadline_positive task_deadline tsk ∧
        task_cost_le_deadline task_cost task_deadline tsk ∧
        task_cost_le_period task_cost task_period tsk

    end ValidParameters

  end BasicTask

end SporadicTask

namespace SporadicTaskset

  open SporadicTask

  section TasksetDefs

    def taskset_of (Task : Type _) [DecidableEq Task] [Fintype Task] : Type := Finset Task

    section TasksetProperties
      variable {Task : Type _} [DecidableEq Task]
      variable (task_cost : Task → Time)
      variable (task_period : Task → Time)
      variable (task_deadline : Task → Time)

      variable (ts : List Task)

      def valid_sporadic_taskset :=
        ∀ tsk, tsk ∈ ts → is_valid_sporadic_task task_cost task_period task_deadline tsk

      def implicit_deadline_model :=
        ∀ tsk, tsk ∈ ts → task_deadline tsk = task_period tsk

      def constrained_deadline_model :=
        ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk

      def arbitrary_deadline_model := True

    end TasksetProperties

  end TasksetDefs

end SporadicTaskset

end Prosa.Classic.Model.Arrival.Basic.Task
