-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/exceedance/SBF.v

import Prosa.Analysis.Facts.Model.IdealUniExceed
import Prosa.Analysis.Definitions.Sbf.Sbf
import Prosa.Analysis.Definitions.Sbf.Busy
import Prosa.Analysis.Facts.Behavior.Supply

namespace Prosa.Analysis.Facts.Model.Exceedance.SBF

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.IdealUniExceed
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Sbf.Busy
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Analysis.Facts.Model.IdealUniExceed

/-! A supply bound function for the ideal uniprocessor with exceedance executions: if the exceedance
executions within every busy-interval prefix of a task are bounded by `e`, then `Δ - e` is a valid unit
supply bound function for that task.

Binders follow the elaborated source types: each declaration takes the section inputs and hypotheses it uses,
in their elaborated order. The processor model is the accepted exceedance processor state. The source's
section-local instance `EPS_SBF_inst` (the SBF `eps_sbf e` registered as a `SupplyBoundFunction`) is the
definition of the same name below, and the SBF is applied through its accepted class field. Representation:
a Boolean in `Prop` position is `= true`; `a <= b <= c` is a Boolean conjunction of decides;
`\sum_(t1 <= t < t2) F t` is the `Finset.Ico` sum over `Nat` (= `instant`); `nat_of_bool` is `Bool.toNat`. -/

/-- The SBF that subtracts a constant exceedance budget `e` from the interval length. -/
def eps_sbf (e : work) (Δ : Nat) : work := Δ - e

/-- LEAN_HELPER for the source's section-local instance `EPS_SBF_inst`: `eps_sbf e` as a supply bound
function. -/
@[instance_reducible] def EPS_SBF_inst (e : work) : SupplyBoundFunction := ⟨eps_sbf e⟩

/-- In a busy-interval prefix of a job of `tsk`, the blackout up to any point of the prefix is bounded
by `e`. -/
theorem blackout_during_bounded {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [JobArrival Job] [JLFP_policy Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (exceedance_proc_state Job)) (e : work) (tsk : Task) :
    (∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
      busy_interval_prefix arr_seq sched j t1 t2 →
      ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (is_exceedance_exec (sched t)).toNat ≤ e) →
    ∀ (j : Job) (t1 t2 : instant) (t : Nat), arrives_in arr_seq j → job_of_task tsk j = true →
      busy_interval_prefix arr_seq sched j t1 t2 → (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      blackout_during sched t1 t ≤ e := by
  intro hbound j t1 t2 t harr htsk hbip hint
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hint
  have hsub : blackout_during sched t1 t ≤ ∑ t' ∈ Finset.Ico t1 t2, (is_exceedance_exec (sched t')).toNat := by
    unfold blackout_during
    calc ∑ t' ∈ Finset.Ico t1 t, (is_blackout sched t').toNat
        = ∑ t' ∈ Finset.Ico t1 t, (is_exceedance_exec (sched t')).toNat := by
          apply Finset.sum_congr rfl
          intro t' _
          rw [blackout_implies_exceedance_execution]
      _ ≤ ∑ t' ∈ Finset.Ico t1 t2, (is_exceedance_exec (sched t')).toNat :=
          Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hint.2)
  exact Nat.le_trans hsub (hbound j t1 t2 harr htsk hbip)

/-- `eps_sbf e` is a valid busy-interval SBF. -/
theorem eps_sbf_is_valid {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [JobArrival Job] [JLFP_policy Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (exceedance_proc_state Job)) (e : work) (tsk : Task) :
    (∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
      busy_interval_prefix arr_seq sched j t1 t2 →
      ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (is_exceedance_exec (sched t)).toNat ≤ e) →
    valid_busy_sbf arr_seq sched tsk (EPS_SBF_inst e).supply_bound_function := by
  intro hbound
  refine ⟨by show 0 - e = 0; exact Nat.zero_sub _, ?_⟩
  intro j t1 t2 harr ⟨htsk, hbip⟩ t ⟨h1, h2⟩
  obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le h1
  have hb := blackout_during_bounded arr_seq sched e tsk hbound j t1 t2 (t1 + δ) harr htsk hbip
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩)
  rw [supply_during_complement sched eps_is_unit_supply t1 δ]
  show t1 + δ - t1 - e ≤ δ - blackout_during sched t1 (t1 + δ)
  ((try dsimp only [instant, duration, work] at *); omega)

/-- `eps_sbf e` grows by at most one per instant. -/
theorem eps_sbf_is_unit (e : work) : unit_supply_bound_function (EPS_SBF_inst e).supply_bound_function := by
  intro δ
  show δ + 1 - e ≤ δ - e + 1
  ((try dsimp only [instant, duration, work] at *); omega)

end Prosa.Analysis.Facts.Model.Exceedance.SBF
