-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/arrival_bound.v

import Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

namespace Prosa.Implementation.Definitions.ArrivalBound

open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

/-- The three source task-arrival-bound alternatives, with their payloads. -/
inductive task_arrivals_bound where
  | Periodic : Nat → task_arrivals_bound
  | Sporadic : Nat → task_arrivals_bound
  | ArrivalPrefix : ArrivalCurvePrefix → task_arrivals_bound
  deriving DecidableEq

/-- Source Boolean equality distinguishes constructors and compares the
    payloads with their corresponding decidable equality observations. -/
def task_arrivals_bound_eqdef (tb1 tb2 : task_arrivals_bound) : Bool :=
  match tb1, tb2 with
  | .Periodic p1, .Periodic p2 => decide (p1 = p2)
  | .Sporadic s1, .Sporadic s2 => decide (s1 = s2)
  | .ArrivalPrefix a1, .ArrivalPrefix a2 => decide (a1 = a2)
  | _, _ => false

/-- LEAN_HELPER: the Boolean observer agrees with the generated equality
    decision for this inductive; it is not an additional source declaration. -/
private theorem eqdef_eq_decide (x y : task_arrivals_bound) :
    task_arrivals_bound_eqdef x y = decide (x = y) := by
  cases x <;> cases y <;> simp [task_arrivals_bound_eqdef]

/-- Informative reflection, preserving the source `reflect` truth index. -/
def eqn_task_arrivals_bound (x y : task_arrivals_bound) :
    BoolReflect (x = y) (task_arrivals_bound_eqdef x y) := by
  rw [eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

end Prosa.Implementation.Definitions.ArrivalBound
