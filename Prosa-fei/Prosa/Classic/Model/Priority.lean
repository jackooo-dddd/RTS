-- Translated from: ../rt-proofs/classic/model/priority.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Util.Rel

namespace Prosa.Classic.Model.Priority

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Util.Rel

section PriorityDefs

  variable (Task : Type _) [DecidableEq Task]
  variable (Job : Type _) [DecidableEq Job]

  def FP_policy := Task → Task → Bool

  def JLFP_policy := Job → Job → Bool

  def JLDP_policy := Time → Job → Job → Bool

end PriorityDefs

section Generalization

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_task : Job → Task)

  def FP_to_JLFP (task_hp : FP_policy Task) : JLFP_policy Job :=
    fun (jhigh jlow : Job) =>
      task_hp (job_task jhigh) (job_task jlow)

  def FP_to_JLDP (task_hp : FP_policy Task) : JLDP_policy Job :=
    fun (_t : Time) => FP_to_JLFP job_task task_hp

  def JLFP_to_JLDP (job_hp : JLFP_policy Job) : JLDP_policy Job :=
    fun (_t : Time) => job_hp

end Generalization

section PropertiesFP

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_task : Job → Task)
  variable (task_priority : FP_policy Task)

  def FP_is_reflexive :=
    ∀ x, task_priority x x = true

  def FP_is_irreflexive :=
    ∀ x, task_priority x x = false

  def FP_is_transitive :=
    ∀ y x z, task_priority x y = true → task_priority y z = true → task_priority x z = true

  section Antisymmetry

    variable (ts : List Task)

    def FP_is_total_over_task_set :=
      total_over_list task_priority ts

    def FP_is_antisymmetric_over_task_set :=
      antisymmetric_over_list task_priority ts

  end Antisymmetry

end PropertiesFP

section PropertiesJLFP

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_task : Job → Task)
  variable (job_arrival : Job → Time)
  variable (arr_seq : arrival_sequence Job)
  variable (job_priority : JLFP_policy Job)

  def JLFP_is_reflexive :=
    ∀ x, job_priority x x = true

  def JLFP_is_irreflexive :=
    ∀ x, job_priority x x = false

  def JLFP_is_transitive :=
    ∀ y x z, job_priority x y = true → job_priority y z = true → job_priority x z = true

  def JLFP_is_total :=
    ∀ j1 j2,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      (job_priority j1 j2 = true ∨ job_priority j2 j1 = true)

  def JLFP_respects_sequential_jobs :=
    ∀ j1 j2,
      job_task j1 = job_task j2 →
      job_arrival j1 ≤ job_arrival j2 →
      job_priority j1 j2 = true

end PropertiesJLFP

section PropertiesJLDP

  variable {Job : Type _} [DecidableEq Job]
  variable (arr_seq : arrival_sequence Job)
  variable (job_priority : JLDP_policy Job)

  def JLDP_is_reflexive :=
    ∀ t, ∀ x, job_priority t x x = true

  def JLDP_is_irreflexive :=
    ∀ t, ∀ x, job_priority t x x = false

  def JLDP_is_transitive :=
    ∀ t, ∀ y x z, job_priority t x y = true → job_priority t y z = true → job_priority t x z = true

  def JLDP_is_total :=
    ∀ j1 j2 t,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      (job_priority t j1 j2 = true ∨ job_priority t j2 j1 = true)

end PropertiesJLDP

section KnownFPPolicies

  variable {Job : Type _} [DecidableEq Job]
  variable {Task : Type _} [DecidableEq Task]
  variable (task_period : Task → Time)
  variable (task_deadline : Task → Time)
  variable (job_arrival : Job → Time)
  variable (job_task : Job → Task)

  def RM (tsk1 tsk2 : Task) : Bool :=
    decide (task_period tsk1 ≤ task_period tsk2)

  def DM (tsk1 tsk2 : Task) : Bool :=
    decide (task_deadline tsk1 ≤ task_deadline tsk2)

  section Properties

    theorem RM_is_reflexive : FP_is_reflexive (RM task_period) := by
      intro x; simp [FP_is_reflexive, RM]

    theorem RM_is_transitive : FP_is_transitive (RM task_period) := by
      intro y x z hxy hyz
      simp [RM] at *
      exact Nat.le_trans hxy hyz

    theorem DM_is_reflexive : FP_is_reflexive (DM task_deadline) := by
      intro x; simp [DM]

    theorem DM_is_transitive : FP_is_transitive (DM task_deadline) := by
      intro y x z hxy hyz
      simp [DM] at *
      exact Nat.le_trans hxy hyz

    theorem any_reflexive_FP_respects_sequential_jobs
        (job_priority : FP_policy Task)
        (h_refl : FP_is_reflexive job_priority) :
        JLFP_respects_sequential_jobs
          job_task job_arrival (FP_to_JLFP job_task job_priority) := by
      intro j1 j2 htsk _
      simp [FP_to_JLFP, htsk]
      exact h_refl (job_task j2)

  end Properties

end KnownFPPolicies

section KnownJLFPPolicies

  section EDF

    variable {Job : Type _} [DecidableEq Job]
    variable (job_arrival : Job → Time)
    variable (job_deadline : Job → Time)
    variable (arr_seq : arrival_sequence Job)

    def EDF (j1 j2 : Job) : Bool :=
      decide (job_arrival j1 + job_deadline j1 ≤ job_arrival j2 + job_deadline j2)

    section Properties

      theorem EDF_is_reflexive : JLFP_is_reflexive (EDF job_arrival job_deadline) := by
        intro j; simp [EDF]

      theorem EDF_is_transitive : JLFP_is_transitive (EDF job_arrival job_deadline) := by
        intro y x z hxy hyz
        simp [EDF] at *
        exact Nat.le_trans hxy hyz

      theorem EDF_is_total : JLFP_is_total arr_seq (EDF job_arrival job_deadline) := by
        intro j1 j2 _ _
        simp only [EDF, decide_eq_true_eq]
        exact le_total _ _

    end Properties

  end EDF

  section EDFwithTasks

    variable {Task : Type _} [DecidableEq Task]
    variable (task_deadline : Task → Time)
    variable {Job : Type _} [DecidableEq Job]
    variable (job_arrival : Job → Time)
    variable (job_task : Job → Task)

    def job_relative_dealine (j : Job) : Time := task_deadline (job_task j)

    theorem EDF_respects_sequential_jobs :
        JLFP_respects_sequential_jobs
          job_task job_arrival (EDF job_arrival (job_relative_dealine task_deadline job_task)) := by
      intro j1 j2 htsk harr
      simp [EDF, job_relative_dealine, htsk]
      omega

  end EDFwithTasks

end KnownJLFPPolicies

section PossibleInterferingTasks

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable (task_cost : sporadic_task → Time)
  variable (task_period : sporadic_task → Time)
  variable (task_deadline : sporadic_task → Time)

  section FP

    variable (higher_eq_priority : FP_policy sporadic_task)
    variable (tsk : sporadic_task)
    variable (tsk_other : sporadic_task)

    def higher_priority_task : Bool :=
      higher_eq_priority tsk_other tsk && decide (tsk_other ≠ tsk)

  end FP

  section JLFP

    variable (tsk : sporadic_task)
    variable (tsk_other : sporadic_task)

    def different_task : Bool := decide (tsk_other ≠ tsk)

  end JLFP

end PossibleInterferingTasks

end Prosa.Classic.Model.Priority
