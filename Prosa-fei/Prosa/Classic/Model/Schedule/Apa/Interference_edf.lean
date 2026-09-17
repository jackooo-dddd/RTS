-- Translated from: ../rt-proofs/classic/model/schedule/apa/interference_edf.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Apa.Interference_edf

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Schedule
open Classical

noncomputable section

def JLFP_policy (Job : Type _) := Job → Job → Bool

def EDF {Job : Type _} (job_arrival : Job → Time) (job_deadline : Job → Time)
    (j1 j2 : Job) : Bool :=
  decide (job_arrival j1 + job_deadline j1 ≤ job_arrival j2 + job_deadline j2)

def respects_JLFP_policy_under_weak_APA
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : ℕ}
    (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu →
    higher_eq_priority j_hp j = true

def job_interference
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time) (job_task : Job → sporadic_task)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus)
    (j job_other : Job) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      (if backlogged job_arrival job_cost sched j t then 1 else 0) *
      (if can_execute_on alpha (job_task j) cpu then 1 else 0) *
      (if scheduled_on sched job_other cpu t then 1 else 0)

namespace InterferenceEDF

section Lemmas

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (alpha : task_affinity sporadic_task num_cpus)

variable (H_scheduler_uses_EDF :
  respects_JLFP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
    (EDF job_arrival job_deadline))
include H_scheduler_uses_EDF

theorem interference_under_edf_implies_shorter_deadlines
    (j j' : Job) (t1 t2 : Time) :
    arrives_in arr_seq j' →
    job_interference job_arrival job_cost job_task sched alpha j' j t1 t2 ≠ 0 →
    job_arrival j + job_deadline j ≤ job_arrival j' + job_deadline j' := by
  intro ARR' INTERF
  unfold job_interference at INTERF
  by_contra H_le
  push_neg at H_le
  apply INTERF
  apply Finset.sum_eq_zero
  intro t _ht
  apply Finset.sum_eq_zero
  intro cpu _hcpu
  by_cases hback : backlogged job_arrival job_cost sched j' t
  · by_cases hcan : can_execute_on alpha (job_task j') cpu
    · by_cases hsched : scheduled_on sched j cpu t = true
      · exfalso
        have hedf := H_scheduler_uses_EDF j' j cpu t ARR' hback hsched hcan
        unfold EDF at hedf
        have h := decide_eq_true_eq.mp hedf
        exact Nat.not_lt.mpr h H_le
      · simp [hsched]
    · simp [hcan]
  · simp [hback]

end Lemmas

end InterferenceEDF

end

end Prosa.Classic.Model.Schedule.Apa.Interference_edf
