-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/tactics.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 6)

import Prosa.Util.Tactics

/-!
Basic Boolean lemmas of the classic tactic library (based on Viktor Vafeiadis'
`Vbase.v`).

Representation notes:
* The source's tactics (`done`, `des`, `desf`, `clarify`, …), hint databases and
  the notation `eqxx := beq_refl` have no Lean counterpart; only the named lemmas
  are declarations.  The source re-exports the official v0.6 `util/tactics.v`,
  mirrored by the `export` of the accepted `Prosa.Util.Tactics` below.
* The source sets `Implicit Arguments`, so every argument determined by a later
  one is implicit (`About` prints `[T]`, `[b1 b2]`, …); they are Lean implicit
  binders.
* `x == y` is `decide (x = y)`; `is_true b` is `b = true`; `negb b` is `!b`; the
  Boolean chain `x1 <= x2 <= x3` is `(decide (x1 ≤ x2) && decide (x2 ≤ x3)) = true`
  and `x < y` is MathComp's `x.+1 <= y`, written `x < y`.
* `reflect P b` is the informative `BoolReflect P b` (as in the accepted v0.6
  files), defined below as a Lean helper.
-/

-- The source names (`vlib__…`) are kept verbatim.
set_option linter.style.nameCheck false

namespace Prosa.Classic.Util.Tactics

export Prosa.Util.Tactics (neqP modusponens)

universe u

/-- LEAN_HELPER: informative Boolean reflection, the Lean form of `reflect`. -/
inductive BoolReflect (P : Prop) : Bool → Type where
  | isTrue : P → BoolReflect P true
  | isFalse : ¬ P → BoolReflect P false

def vlib__internal_eqP {T : Type u} [DecidableEq T] (x y : T) :
    BoolReflect (x = y) (decide (x = y)) :=
  if h : x = y then (decide_eq_true h) ▸ BoolReflect.isTrue h
  else (decide_eq_false h) ▸ BoolReflect.isFalse h

theorem beq_refl {T : Type u} [DecidableEq T] (x : T) : decide (x = x) = true := by
  simp

theorem beq_sym {T : Type u} [DecidableEq T] (x y : T) :
    decide (x = y) = decide (y = x) :=
  decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩

theorem vlib__negb_rewrite {b : Bool} : (!b) = true → b = false := by
  cases b <;> simp

theorem vlib__andb_split {b1 b2 : Bool} : (b1 && b2) = true → b1 = true ∧ b2 = true := by
  cases b1 <;> cases b2 <;> simp

theorem vlib__nandb_split {b1 b2 : Bool} : (b1 && b2) = false → b1 = false ∨ b2 = false := by
  cases b1 <;> cases b2 <;> simp

theorem vlib__orb_split {b1 b2 : Bool} : (b1 || b2) = true → b1 = true ∨ b2 = true := by
  cases b1 <;> cases b2 <;> simp

theorem vlib__norb_split {b1 b2 : Bool} : (b1 || b2) = false → b1 = false ∧ b2 = false := by
  cases b1 <;> cases b2 <;> simp

theorem vlib__eqb_split {b1 b2 : Bool} :
    (b1 = true → b2 = true) → (b2 = true → b1 = true) → b1 = b2 := by
  cases b1 <;> cases b2 <;> simp

theorem vlib__beq_rewrite {T : Type u} [DecidableEq T] {x1 x2 : T} :
    decide (x1 = x2) = true → x1 = x2 := by
  simp

theorem vlib__leq_split {x1 x2 x3 : Nat} :
    x1 ≤ x2 → x2 ≤ x3 → (decide (x1 ≤ x2) && decide (x2 ≤ x3)) = true := by
  intro h1 h2
  simp [h1, h2]

theorem vlib__ltn_split1 {x1 x2 x3 : Nat} :
    x1 ≤ x2 → x2 < x3 → (decide (x1 ≤ x2) && decide (x2 < x3)) = true := by
  intro h1 h2
  simp [h1, h2]

theorem vlib__ltn_split2 {x1 x2 x3 : Nat} :
    x1 < x2 → x2 ≤ x3 → (decide (x1 < x2) && decide (x2 ≤ x3)) = true := by
  intro h1 h2
  simp [h1, h2]

end Prosa.Classic.Util.Tactics
