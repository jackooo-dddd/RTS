-- Translated from: ../rt-proofs/classic/model/schedule/global/jitter/interference_edf.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
import Prosa.Classic.Model.Priority
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Priority
open Schedule

namespace InterferenceEDF

section Lemmas

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_jitter : Job → Time)

variable (arr_seq : arrival_sequence Job)

variable (num_cpus : ℕ)
variable (sched : schedule Job num_cpus)

noncomputable def respects_JLFP_policy_edf
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged_jitter job_arrival job_cost job_jitter sched j t →
    scheduled sched j_hp t →
    higher_eq_priority j_hp j = true

open Classical in
noncomputable def job_interference_edf
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j' j : Job) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      (if backlogged_jitter job_arrival job_cost job_jitter sched j' t then 1 else 0) *
      (if scheduled_on sched j cpu t then 1 else 0)

variable (H_scheduler_uses_EDF :
  respects_JLFP_policy_edf job_arrival job_cost job_jitter arr_seq sched
    (EDF job_arrival job_deadline))

include H_scheduler_uses_EDF

theorem interference_under_edf_implies_shorter_deadlines :
    ∀ j j' t1 t2,
      arrives_in arr_seq j →
      arrives_in arr_seq j' →
      job_interference_edf job_arrival job_cost job_jitter sched j' j t1 t2 ≠ 0 →
      job_arrival j + job_deadline j ≤ job_arrival j' + job_deadline j' := by
  intro j j' t1 t2 ARR ARR' INTERF
  by_contra H_not_le
  apply INTERF
  unfold job_interference_edf
  apply Finset.sum_eq_zero
  intro t _ht
  apply Finset.sum_eq_zero
  intro cpu _hcpu
  by_cases hb : backlogged_jitter job_arrival job_cost job_jitter sched j' t
  · by_cases hs : scheduled_on sched j cpu t = true
    · exfalso
      apply H_not_le
      have hsched : scheduled sched j t := ⟨cpu, hs⟩
      have hprio := H_scheduler_uses_EDF j' j t ARR' hb hsched
      unfold EDF at hprio
      rw [decide_eq_true_eq] at hprio
      exact hprio
    · rw [if_pos hb, if_neg hs, Nat.mul_zero]
  · rw [if_neg hb, Nat.zero_mul]

end Lemmas

end InterferenceEDF

end Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf
