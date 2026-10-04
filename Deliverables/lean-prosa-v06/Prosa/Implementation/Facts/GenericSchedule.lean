-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/facts/generic_schedule.v

import Prosa.Implementation.Definitions.GenericScheduler
import Prosa.Analysis.Facts.Transform.ReplaceAt

namespace Prosa.Implementation.Facts.GenericSchedule

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Implementation.Definitions.GenericScheduler

/-! Properties of the generic reference scheduler. Binders follow the
elaborated source types. Representation: the section-local
`prefix t := if t is t'.+1 then schedule_up_to … t' else empty_schedule …`
is inlined as a `match` on `t`, as in the elaborated types; `t.+1` is
`t + 1`. -/

universe u v w

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState.{u, v, w} Job}

theorem schedule_up_to_def (policy : PointwisePolicy PState) (idle_state : PState.State)
    (t : instant) :
    schedule_up_to policy idle_state t t =
      policy (match t with
        | 0 => empty_schedule idle_state
        | t' + 1 => schedule_up_to policy idle_state t') t := by
  cases t <;> simp [schedule_up_to, replace_at]

theorem schedule_up_to_unfold (policy : PointwisePolicy PState) (idle_state : PState.State)
    (h t : instant) :
    schedule_up_to policy idle_state h t =
      replace_at (match h with
          | 0 => empty_schedule idle_state
          | t' + 1 => schedule_up_to policy idle_state t') h
        (policy (match h with
          | 0 => empty_schedule idle_state
          | t' + 1 => schedule_up_to policy idle_state t') h) t := by
  cases h <;> rfl

theorem schedule_up_to_widen (policy : PointwisePolicy PState) (idle_state : PState.State)
    (h t : Nat) :
    t ≤ h → schedule_up_to policy idle_state h t = schedule_up_to policy idle_state (h + 1) t := by
  intro hle
  show schedule_up_to policy idle_state h t =
    replace_at (schedule_up_to policy idle_state h) (h + 1)
      (policy (schedule_up_to policy idle_state h) (h + 1)) t
  have hne : (h + 1 == t) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; omega
  simp only [replace_at, hne]
  rfl

theorem schedule_up_to_empty (policy : PointwisePolicy PState) (idle_state : PState.State)
    (h t : Nat) :
    h < t → schedule_up_to policy idle_state h t = idle_state := by
  induction h with
  | zero =>
      intro hlt
      have hne : (0 == t) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      show replace_at (empty_schedule idle_state) 0 (policy (empty_schedule idle_state) 0) t = idle_state
      simp only [replace_at, hne]
      rfl
  | succ h ih =>
      intro hlt
      have hne : (h + 1 == t) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      show replace_at (schedule_up_to policy idle_state h) (h + 1)
        (policy (schedule_up_to policy idle_state h) (h + 1)) t = idle_state
      simp only [replace_at, hne]
      exact ih (by omega)

theorem schedule_up_to_prefix_inclusion (policy : PointwisePolicy PState)
    (idle_state : PState.State) (h1 h2 : Nat) :
    h1 ≤ h2 → ∀ t : Nat, t ≤ h1 →
      schedule_up_to policy idle_state h1 t = schedule_up_to policy idle_state h2 t := by
  intro hle t ht
  induction h2, hle using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      rw [ih]
      exact schedule_up_to_widen policy idle_state k t (Nat.le_trans ht hk)

theorem schedule_up_to_identical_prefix (policy : PointwisePolicy PState)
    (idle_state : PState.State) (h t : Nat) :
    t ≤ h + 1 →
      identical_prefix (schedule_up_to policy idle_state h) (generic_schedule policy idle_state) t := by
  intro hle t' hlt
  unfold generic_schedule
  exact (schedule_up_to_prefix_inclusion policy idle_state t' h (by omega') t' (Nat.le_refl _)).symm

end Prosa.Implementation.Facts.GenericSchedule
