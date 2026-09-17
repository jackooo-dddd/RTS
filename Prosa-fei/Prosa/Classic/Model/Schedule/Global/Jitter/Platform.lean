-- Translated from: ../rt-proofs/classic/model/schedule/global/jitter/platform.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Priority

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Platform

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Job (valid_sporadic_job)
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence (arrival_sequence arrives_in)
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Priority
open Schedule

section Properties

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)

variable (arr_seq : arrival_sequence Job)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

section Execution

  def work_conserving :=
    ∀ j t,
      arrives_in arr_seq j →
      backlogged_jitter job_arrival job_cost job_jitter sched j t →
      ∀ cpu, ∃ j_other, scheduled_on sched j_other cpu t = true

  def work_conserving_count :=
    ∀ j t,
      arrives_in arr_seq j →
      backlogged_jitter job_arrival job_cost job_jitter sched j t →
      (jobs_scheduled_at sched t).length = num_cpus

end Execution

section FP

  variable (higher_eq_priority : FP_policy sporadic_task)

  def respects_FP_policy :=
    ∀ j j_hp t,
      arrives_in arr_seq j →
      backlogged_jitter job_arrival job_cost job_jitter sched j t →
      scheduled sched j_hp t →
      higher_eq_priority (job_task j_hp) (job_task j) = true

end FP

section JLFP

  variable (higher_eq_priority : JLFP_policy Job)

  def respects_JLFP_policy :=
    ∀ j j_hp t,
      arrives_in arr_seq j →
      backlogged_jitter job_arrival job_cost job_jitter sched j t →
      scheduled sched j_hp t →
      higher_eq_priority j_hp j = true

end JLFP

section JLDP

  variable (higher_eq_priority : JLDP_policy Job)

  def respects_JLDP_policy :=
    ∀ j j_hp t,
      arrives_in arr_seq j →
      backlogged_jitter job_arrival job_cost job_jitter sched j t →
      scheduled sched j_hp t →
      higher_eq_priority t j_hp j = true

end JLDP

section Lemmas

  variable (H_valid_job_parameters :
    ∀ j,
      arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

  section EquivalentDefinitions

    theorem work_conserving_eq_work_conserving_count :
        work_conserving job_arrival job_cost job_jitter arr_seq sched ↔
        work_conserving_count job_arrival job_cost job_jitter arr_seq sched := by
      unfold work_conserving work_conserving_count
      constructor
      · -- Forward: ∀ cpu, ∃ j_other, scheduled_on ... → length = num_cpus
        intro h_wc j t h_arr h_back
        have h_all := h_wc j t h_arr h_back
        -- Use: every cpu has a job means sched cpu t ≠ none for all cpu
        -- So each cpu contributes 1 job to jobs_scheduled_at
        -- We need length = num_cpus
        -- Key helper: sched cpu t is Some for every cpu
        have h_some : ∀ cpu : Fin num_cpus, ∃ j', sched cpu t = some j' := by
          intro cpu
          obtain ⟨j_other, h_on⟩ := h_all cpu
          unfold scheduled_on at h_on
          exact ⟨j_other, eq_of_beq h_on⟩
        -- Now prove via bigcat_ord length
        show (jobs_scheduled_at sched t).length = num_cpus
        unfold jobs_scheduled_at
        rw [Prosa.Classic.Util.Bigcat.size_bigcat_ord]
        trans (∑ _i : Fin num_cpus, 1)
        · apply Finset.sum_congr rfl
          intro i _
          obtain ⟨j', hj'⟩ := h_some i
          rw [hj']
          rfl
        · rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
      · -- Backward: length = num_cpus → ∀ cpu, ∃ j_other, scheduled_on ...
        intro h_wcc j t h_arr h_back cpu
        specialize h_wcc j t h_arr h_back
        cases h_eq : sched cpu t with
        | some j0 =>
          exact ⟨j0, by unfold scheduled_on; rw [h_eq]; exact beq_self_eq_true _⟩
        | none =>
          exfalso
          -- length = num_cpus but cpu contributes 0 and others contribute ≤ 1
          -- so length < num_cpus, contradiction
          have h_lt : (jobs_scheduled_at sched t).length < num_cpus := by
            unfold jobs_scheduled_at
            rw [Prosa.Classic.Util.Bigcat.size_bigcat_ord]
            calc ∑ i : Fin num_cpus, (match sched i t with | some j => [j] | none => []).length
                = (match sched cpu t with | some j => [j] | none => []).length +
                  ∑ i ∈ Finset.univ.erase cpu, (match sched i t with | some j => [j] | none => []).length := by
                    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ cpu)]
              _ = 0 + ∑ i ∈ Finset.univ.erase cpu, (match sched i t with | some j => [j] | none => []).length := by
                    rw [h_eq]; rfl
              _ = ∑ i ∈ Finset.univ.erase cpu, (match sched i t with | some j => [j] | none => []).length := by
                    omega
              _ ≤ ∑ _i ∈ Finset.univ.erase cpu, 1 := by
                    apply Finset.sum_le_sum
                    intro i _
                    cases sched i t with
                    | some _ => rfl
                    | none => exact Nat.zero_le _
              _ = (Finset.univ.erase cpu).card := by simp
              _ < Finset.univ.card := Finset.card_erase_lt_of_mem (Finset.mem_univ cpu)
              _ = num_cpus := Fintype.card_fin num_cpus
          omega

  end EquivalentDefinitions

end Lemmas

end Properties

end Prosa.Classic.Model.Schedule.Global.Jitter.Platform
