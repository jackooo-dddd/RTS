import Validation.fixtures.translation_order.NondecreasingComputationInterface

namespace Prosa.Validation.NondecreasingNormalization

open Prosa.Util.Nondecreasing
open Prosa.Validation.NondecreasingInterface

/-- Kernel guards for the exact `Meta.reduceAll` normal forms exported from
    this compiled snapshot. The only non-conversion step is case analysis on
    `Option`; changing either production body or normal form invalidates them. -/
private theorem option_getD_zero_eq_rec (o : Option Nat) :
    o.getD 0 = @Option.rec Nat (fun _ => Nat) 0 (fun val => val) o := by
  cases o <;> rfl

theorem nthD_guard :
    nthD = fun (xs : List Nat) (n : Nat) =>
      @Option.rec Nat (fun _ => Nat) 0 (fun val => val)
        (List.get?Internal xs n) := by
  funext xs n
  simp [nthD, option_getD_zero_eq_rec]

theorem nondecreasing_sequence_guard (xs : List Nat) :
    nondecreasing_sequence xs ↔
      ∀ n₁ n₂,
        (n₁ ≤ n₂ ∧ n₂ < xs.length) →
          Nat.le
            (@Option.rec Nat (fun _ => Nat) 0 (fun val => val)
              (List.get?Internal xs n₁))
            (@Option.rec Nat (fun _ => Nat) 0 (fun val => val)
              (List.get?Internal xs n₂)) := by
  simp [nondecreasing_sequence, option_getD_zero_eq_rec]

theorem increasing_sequence_guard (xs : List Nat) :
    increasing_sequence xs ↔
      ∀ n₁ n₂,
        (n₁ < n₂ ∧ n₂ < xs.length) →
          Nat.le
            (Nat.succ
              (@Option.rec Nat (fun _ => Nat) 0 (fun val => val)
                (List.get?Internal xs n₁)))
            (@Option.rec Nat (fun _ => Nat) 0 (fun val => val)
              (List.get?Internal xs n₂)) := by
  simp [increasing_sequence, option_getD_zero_eq_rec]

theorem distances_guard (xs : List Nat) :
    distances xs =
      List.map (fun (p : Nat × Nat) => Nat.sub p.2 p.1)
        (List.zipWith Prod.mk xs (List.drop 1 xs)) := rfl

#print axioms nthD_guard
#print axioms nondecreasing_sequence_guard
#print axioms increasing_sequence_guard
#print axioms distances_guard

end Prosa.Validation.NondecreasingNormalization
