import Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

#check @ArrivalCurvePrefix
#check @step_at
#check @extrapolated_arrival_curve
#check @large_horizon_P
#check @valid_arrival_curve_prefix_P
#print sortedBool
#print sortedBoolFrom
#print axioms large_horizon_iff
#print axioms large_horizon_P
#print axioms valid_arrival_curve_prefix_P

example {α : Type _} (R : α → α → Bool) (x : α) :
    sortedBoolFrom R x [] = true := by rfl
example {α : Type _} (R : α → α → Bool) (x y : α) (rest : List α) :
    sortedBoolFrom R x (y :: rest) = (R x y && sortedBoolFrom R y rest) := by rfl
example {α : Type _} (R : α → α → Bool) (x : α) (rest : List α) :
    sortedBool R (x :: rest) = sortedBoolFrom R x rest := by rfl
