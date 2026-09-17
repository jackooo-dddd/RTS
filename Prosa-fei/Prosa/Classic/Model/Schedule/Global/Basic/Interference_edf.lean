-- Translated from: ../rt-proofs/classic/model/schedule/global/basic/interference_edf.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Priority
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Basic.Interference_edf

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Priority
open Schedule

attribute [local instance] Classical.propDecidable

namespace InterferenceEDF

section Lemmas

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)

variable {arr_seq : arrival_sequence Job}

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

noncomputable def job_interference (j job_other : Job) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if (backlogged job_arrival job_cost sched j t ∧
          scheduled_on sched job_other cpu t = true) then 1 else 0

def respects_JLFP_policy (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled sched j_hp t →
    higher_eq_priority j_hp j = true

variable (H_scheduler_uses_EDF :
  respects_JLFP_policy (arr_seq := arr_seq) job_arrival job_cost sched
    (EDF job_arrival job_deadline))
include H_scheduler_uses_EDF

theorem interference_under_edf_implies_shorter_deadlines :
    ∀ (j j' : Job) (t1 t2 : Time),
      arrives_in arr_seq j →
      arrives_in arr_seq j' →
      job_interference job_arrival job_cost sched j' j t1 t2 ≠ 0 →
      job_arrival j + job_deadline j ≤ job_arrival j' + job_deadline j' := by
  intro j j' t1 t2 hArr1 hArr2 hInterf
  unfold job_interference at hInterf
  -- Since the sum is nonzero, there exist t and cpu where the condition holds
  -- We prove this by contradiction: if no such t and cpu exist, the sum is 0
  suffices h : ∃ t ∈ Finset.Ico t1 t2, ∃ cpu : Fin num_cpus,
      (backlogged job_arrival job_cost sched j' t ∧
       scheduled_on sched j cpu t = true) by
    obtain ⟨t, _, cpu, hBack, hSchedOn⟩ := h
    have hSched : scheduled sched j t := ⟨cpu, hSchedOn⟩
    have hPrio := H_scheduler_uses_EDF j' j t hArr2 hBack hSched
    unfold EDF at hPrio
    rw [decide_eq_true_eq] at hPrio
    exact hPrio
  by_contra h_none
  apply hInterf
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro cpu _
  split_ifs with h_cond
  · exfalso; apply h_none; exact ⟨t, ht, cpu, h_cond⟩
  · rfl

end Lemmas

end InterferenceEDF

end Prosa.Classic.Model.Schedule.Global.Basic.Interference_edf
