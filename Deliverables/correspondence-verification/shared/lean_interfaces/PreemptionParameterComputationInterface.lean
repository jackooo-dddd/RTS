import Prosa.Model.Preemption.Parameter
import Validation.fixtures.translation_order.NondecreasingComputationInterface
import Validation.fixtures.translation_order.ServiceComputationInterface
import Validation.fixtures.translation_order.ArrivalSequenceComputationInterface

/-!
Export root for `model/preemption/parameter.v`: the production declarations,
the accepted Service / arrival-sequence / Nondecreasing computation
interfaces, and kernel-checked constructor equations for the Nat-list
operations occurring in the definition bodies (filter over a Nat predicate,
membership, `range`, `max0` via `Nat.max` folding, `last0`, Nat equality
decisions).  Every equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.PreemptionParameterInterface

open Prosa.Behavior.Job
open Prosa.Util.List
open Prosa.Model.Preemption.Parameter

def natFilter (p : Nat → Bool) (xs : List Nat) : List Nat := xs.filter p

theorem production_natFilter_nil (p : Nat → Bool) : natFilter p [] = [] := rfl

theorem production_natFilter_cons_true (p : Nat → Bool) (x : Nat) (xs : List Nat)
    (h : p x = true) : natFilter p (x :: xs) = x :: natFilter p xs := by
  simp [natFilter, h]

theorem production_natFilter_cons_false (p : Nat → Bool) (x : Nat) (xs : List Nat)
    (h : p x = false) : natFilter p (x :: xs) = natFilter p xs := by
  simp [natFilter, h]

theorem production_job_preemption_points_eq {Job : JobType} [DecidableEq Job] [JobCost Job]
    [JobPreemptable Job] (j : Job) :
    job_preemption_points j = natFilter (fun ρ => job_preemptable j ρ) (range 0 (job_cost j)) :=
  rfl

theorem production_range_eq (a b : Nat) : range a b = List.range' a (b + 1 - a) := rfl

def natMem (x : Nat) (xs : List Nat) : Bool := decide (x ∈ xs)

theorem production_mem_eq (x : Nat) (xs : List Nat) : decide (x ∈ xs) = natMem x xs := rfl

theorem production_natMem_nil (x : Nat) : natMem x [] = false := by simp [natMem]

theorem production_natMem_cons (x y : Nat) (ys : List Nat) :
    natMem x (y :: ys) = (decide (x = y) || natMem x ys) := by
  simp [natMem, List.mem_cons]

theorem production_nat_decide_eq_true (x y : Nat) (h : x = y) : decide (x = y) = true := by
  simp [h]

theorem production_nat_decide_eq_false (x y : Nat) (h : ¬ x = y) : decide (x = y) = false := by
  simp [h]

def natFoldMax (z : Nat) (xs : List Nat) : Nat := xs.foldl Nat.max z

theorem production_max0_eq (xs : List Nat) : max0 xs = natFoldMax 0 xs := rfl

theorem production_natFoldMax_nil (z : Nat) : natFoldMax z [] = z := rfl

theorem production_natFoldMax_cons (z x : Nat) (xs : List Nat) :
    natFoldMax z (x :: xs) = natFoldMax (Nat.max z x) xs := rfl

theorem production_max_of_le (a b : Nat) (h : a ≤ b) : Nat.max a b = b := Nat.max_eq_right h

theorem production_max_of_ge (a b : Nat) (h : b ≤ a) : Nat.max a b = a := Nat.max_eq_left h

theorem production_last0_nil : last0 [] = 0 := rfl

theorem production_last0_single (x : Nat) : last0 [x] = x := rfl

theorem production_last0_cons2 (x y : Nat) (xs : List Nat) :
    last0 (x :: y :: xs) = last0 (y :: xs) := rfl

end Prosa.Validation.PreemptionParameterInterface
