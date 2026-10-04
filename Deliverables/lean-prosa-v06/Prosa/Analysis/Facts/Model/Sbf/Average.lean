-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/sbf/average.v

import Prosa.Model.Priority.Classes
import Prosa.Model.Processor.Supply
import Prosa.Model.Processor.PlatformProperties
import Prosa.Analysis.Definitions.Sbf.Plain
import Prosa.Analysis.Definitions.Sbf.Average

namespace Prosa.Analysis.Facts.Model.Sbf.Average

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Sbf.Plain
open Prosa.Analysis.Definitions.Sbf.Average

/-- `omega'` after unfolding the time/work aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

theorem arm_sbf_monotone (period alloc delay : duration) : sbf_is_monotone (arm_sbf period alloc delay) := by
  intro x y hxy
  have hle := of_decide_eq_true hxy
  apply decide_eq_true
  unfold arm_sbf
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  exact Nat.sub_le_sub_right hle delay

theorem arm_sbf_unit {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (period alloc delay : duration) :
    average_resource_model period alloc delay sched → unit_supply_bound_function (arm_sbf period alloc delay) := by
  intro hmodel δ
  have halloc : alloc ≤ period := hmodel.1
  unfold arm_sbf
  by_cases hdelay : delay ≤ δ
  · have hs : δ + 1 - delay = (δ - delay) + 1 := by omega'
    rw [hs, Nat.succ_mul]
    rcases Nat.eq_zero_or_pos period with h0 | hpos
    · simp [h0]
    · calc ((δ - delay) * alloc + alloc) / period ≤ ((δ - delay) * alloc + period) / period := Nat.div_le_div_right (by omega')
        _ = (δ - delay) * alloc / period + 1 := Nat.add_div_right _ hpos
  · have h1 : δ + 1 - delay = 0 := by omega'
    have h2 : δ - delay = 0 := by omega'
    simp [h1, h2]

theorem arm_sbf_valid {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (period alloc delay : duration) :
    average_resource_model period alloc delay sched →
      valid_supply_bound_function arr_seq sched (arm_sbf period alloc delay) := by
  intro hmodel
  refine ⟨by simp [arm_sbf], ?_⟩
  intro j t1 t2 _ _ t _
  exact hmodel.2 t1 t

end Prosa.Analysis.Facts.Model.Sbf.Average
