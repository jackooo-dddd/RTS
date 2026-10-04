-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/powerset.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 12)

import Mathlib.Data.List.Basic

/-!
The power set of a sequence.

Representation notes:
* `powerset l` maps MathComp's `mask m l` over `enum {: (size l).-tuple bool}`.  The
  Lean helpers below reproduce both exactly: `mask` is MathComp's `mask` (same
  recursion), and `boolTupleEnum n` is the MathComp enumeration of `n.-tuple bool`
  (`FinTuple.enum`: `iter n extend [:: [::]]` with `extend e := flatten (codom (fun x
  => map (cons x) e))`, and `enum bool = [:: true; false]`), so the list order is the
  source order.
* `{subset y <= x}` is `∀ z, z ∈ y → z ∈ x`; `y \in powerset x` in proposition position
  is `y ∈ powerset x`.
-/

namespace Prosa.Classic.Util.Powerset

universe u

/-- LEAN_HELPER: MathComp's `mask m s` (keep `s`'s elements where `m` is `true`). -/
def mask {T : Type u} : List Bool → List T → List T
  | b :: m, x :: s => if b then x :: mask m s else mask m s
  | _, _ => []

/-- LEAN_HELPER: MathComp's enumeration of `n.-tuple bool`, as lists. -/
def boolTupleEnum : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => ([true, false].map (fun x => (boolTupleEnum n).map (x :: ·))).flatten

def powerset {T : Type u} [DecidableEq T] (l : List T) : List (List T) :=
  (boolTupleEnum l.length).map (fun m => mask m l)

/-- LEAN_HELPER: a mask selects a sublist. -/
private theorem mask_subset {T : Type u} :
    ∀ (m : List Bool) (s : List T) (z : T), z ∈ mask m s → z ∈ s
  | b :: m, x :: s, z, h => by
      unfold mask at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mask_subset m s z h')
      · exact List.mem_cons_of_mem _ (mask_subset m s z h)
  | [], _, _, h => by simp [mask] at h
  | _ :: _, [], _, h => by simp [mask] at h

theorem mem_powerset {T : Type u} [DecidableEq T] (x : List T) (y : List T) :
    y ∈ powerset x → ∀ z, z ∈ y → z ∈ x := by
  intro POW z IN
  unfold powerset at POW
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp POW
  exact mask_subset m x z IN

end Prosa.Classic.Util.Powerset
