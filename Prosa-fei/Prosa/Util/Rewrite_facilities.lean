-- Translated from: ../rt-proofs/util/rewrite_facilities.v
import Mathlib.Tactic

namespace Prosa.Util.Rewrite_facilities

namespace RewriteFacilities

lemma diseq {X : Type _} (p : X → Prop) (x y : X) :
    ¬ p x → p y → x ≠ y := by
  intro hnp hp heq
  subst heq
  exact hnp hp

lemma eqprop_to_eqbool {X : Type _} [DecidableEq X] {a b : X} :
    a = b → (a == b) = true := by
  intro h; subst h; simp

lemma eqbool_true {X : Type _} [DecidableEq X] {a b : X} :
    (a == b) = true → (a == b) = true := by
  exact id

lemma eqbool_false {X : Type _} [DecidableEq X] {a b : X} :
    (a != b) = true → (a == b) = false := by
  simp [bne] at *

lemma eqbool_to_eqprop {X : Type _} [DecidableEq X] {a b : X} :
    (a == b) = true → a = b := by
  simp [beq_iff_eq]

lemma neqprop_to_neqbool {X : Type _} [DecidableEq X] {a b : X} :
    a ≠ b → (a != b) = true := by
  simp [bne]

lemma neqbool_to_neqprop {X : Type _} [DecidableEq X] {a b : X} :
    (a != b) = true → a ≠ b := by
  simp [bne]

lemma neq_sym {X : Type _} [DecidableEq X] {a b : X} :
    (a != b) = true → (b != a) = true := by
  simp [bne]
  exact Ne.symm

lemma neq_antirefl {X : Type _} [DecidableEq X] {a : X} :
    (a != a) = false := by
  simp [bne]

lemma option_inj_eq {X : Type _} [DecidableEq X] {a b : X} :
    (a == b) = true → (some a == some b) = true := by
  simp [beq_iff_eq]

lemma option_inj_neq {X : Type _} [DecidableEq X] {a b : X} :
    (a != b) = true → (some a != some b) = true := by
  simp [bne]

section Example

variable {X : Type _} [DecidableEq X]
variable (f : Bool → Bool)
variable (p : X → Prop)
variable (a b : X)
variable (H_pa : p a)
variable (H_npb : ¬ p b)

end Example

end RewriteFacilities

end Prosa.Util.Rewrite_facilities
