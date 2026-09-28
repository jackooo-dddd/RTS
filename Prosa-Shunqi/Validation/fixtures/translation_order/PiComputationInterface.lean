import Prosa.Analysis.Facts.BusyInterval.Pi
import Validation.fixtures.translation_order.HepAtPtComputationInterface
import Validation.fixtures.translation_order.TaskPreemptionParametersComputationInterface

/-!
Export root for `analysis/facts/busy_interval/pi.v`: the production
declarations together with the accepted `hep_at_pt` export root, the accepted
task-preemption-parameters export root, and kernel-checked constructor
equations for the conditional maximum `bigMaxListCond` (the same equations as
the accepted blocking-bound interface, restated here so that the blocking-bound
definitions stay out of this export).  Every equation is proved in Lean and
exported with its proof.
-/

namespace Prosa.Validation.PiInterface

open Prosa.Util.Minmax

universe u

theorem production_bigMaxListCond_nil {X : Type u} (P : X → Bool) (F : X → Nat) :
    bigMaxListCond [] P F = 0 := rfl

theorem production_bigMaxListCond_cons_true {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = true) :
    bigMaxListCond (x :: xs) P F = Nat.max (F x) (bigMaxListCond xs P F) := by
  simp [bigMaxListCond, h]

theorem production_bigMaxListCond_cons_false {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = false) :
    bigMaxListCond (x :: xs) P F = bigMaxListCond xs P F := by
  simp [bigMaxListCond, h]

end Prosa.Validation.PiInterface
