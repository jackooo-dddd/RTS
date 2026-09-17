-- Translated from: ../rt-proofs/classic/util/tactics.v
import Mathlib.Tactic
import Mathlib.Data.Bool.Basic
import Prosa.Util.Tactics

namespace Prosa.Classic.Util.Tactics

lemma vlib__internal_eqP {T : Type _} [DecidableEq T] (x y : T) :
    x = y ↔ (x == y) = true := by
  constructor
  · intro h; subst h; simp
  · intro h; exact of_decide_eq_true h

lemma beq_refl {T : Type _} [DecidableEq T] (x : T) :
    (x == x) = true := by
  simp

lemma beq_sym {T : Type _} [DecidableEq T] (x y : T) :
    (x == y) = (y == x) := by
  simp only [BEq.beq, decide_eq_decide]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

abbrev eqxx := @beq_refl

lemma vlib__negb_rewrite {b : Bool} (h : !b = true) : b = false := by
  cases b <;> simp_all

lemma vlib__andb_split {b1 b2 : Bool} (h : (b1 && b2) = true) :
    b1 = true ∧ b2 = true := by
  cases b1 <;> cases b2 <;> simp_all

lemma vlib__nandb_split {b1 b2 : Bool} (h : (b1 && b2) = false) :
    b1 = false ∨ b2 = false := by
  cases b1 <;> cases b2 <;> simp_all

lemma vlib__orb_split {b1 b2 : Bool} (h : (b1 || b2) = true) :
    b1 = true ∨ b2 = true := by
  cases b1 <;> cases b2 <;> simp_all

lemma vlib__norb_split {b1 b2 : Bool} (h : (b1 || b2) = false) :
    b1 = false ∧ b2 = false := by
  cases b1 <;> cases b2 <;> simp_all

lemma vlib__eqb_split {b1 b2 : Bool} (h1 : b1 = true → b2 = true)
    (h2 : b2 = true → b1 = true) : b1 = b2 := by
  cases b1 <;> cases b2 <;> simp_all

lemma vlib__beq_rewrite {T : Type _} [DecidableEq T] {x1 x2 : T}
    (h : (x1 == x2) = true) : x1 = x2 := by
  exact of_decide_eq_true h

lemma vlib__leq_split {x1 x2 x3 : Nat} (h1 : x1 ≤ x2) (h2 : x2 ≤ x3) :
    x1 ≤ x2 ∧ x2 ≤ x3 := by
  exact ⟨h1, h2⟩

lemma vlib__ltn_split1 {x1 x2 x3 : Nat} (h1 : x1 ≤ x2) (h2 : x2 < x3) :
    x1 ≤ x2 ∧ x2 < x3 := by
  exact ⟨h1, h2⟩

lemma vlib__ltn_split2 {x1 x2 x3 : Nat} (h1 : x1 < x2) (h2 : x2 ≤ x3) :
    x1 < x2 ∧ x2 ≤ x3 := by
  exact ⟨h1, h2⟩

end Prosa.Classic.Util.Tactics
