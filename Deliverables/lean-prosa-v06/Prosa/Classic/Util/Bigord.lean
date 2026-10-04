-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/bigord.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 7)

import Prosa.Util.Bigop
import Mathlib.Data.List.FinRange

/-!
Lemmas about big operators over ordinals.

Representation notes:
* `'I_n` is `Fin n`; `Ordinal LT` is `⟨x, LT⟩`; the coercion to `nat` is `.val`.
* The generic big operator `\big[op/idx]_(i <- r | P i) F i` (no monoid laws) is the
  accepted v0.6 right fold `Prosa.Util.Bigop.bigSeq idx op P F r`, and
  `\big[op/idx]_(i < n | P i) F i` ranges over `'I_n` in increasing order, i.e.
  over `List.finRange n`.
-/

namespace Prosa.Classic.Util.Bigord

open Prosa.Util.Bigop

universe u

/-- If `x < n`, apply `f` to the ordinal `x`; otherwise return the default `x0`. -/
def fun_ord_to_nat {n : Nat} {T : Type u} (x0 : T) (f : Fin n → T) : Nat → T :=
  fun x => if LT : x < n then f ⟨x, LT⟩ else x0

theorem eq_fun_ord_to_nat :
    ∀ (n : Nat) {T : Type u} (x0 : T) (f : Fin n → T) (x : Fin n),
      fun_ord_to_nat x0 f x.val = f x := by
  intro n T x0 f x
  simp [fun_ord_to_nat, x.isLt]

theorem eq_bigr_ord (T : Type u) (n : Nat) (op : T → T → T) (idx : T)
    (r : List (Fin n)) (P : Fin n → Bool) (F1 : Nat → T) (F2 : Fin n → T) :
    (∀ i, P i = true → F1 i.val = F2 i) →
      bigSeq idx op P (fun i => F1 i.val) r = bigSeq idx op P F2 r := by
  intro H
  induction r with
  | nil => rfl
  | cons a r ih =>
      simp only [bigSeq]
      cases hP : P a with
      | false => simp [ih]
      | true => simp [ih, H a hP]

theorem big_mkord_ord {T : Type u} {n : Nat} {op : T → T → T} {idx : T}
    (x0 : T) (P : Fin n → Bool) (F : Fin n → T) :
    bigSeq idx op P F (List.finRange n) =
      bigSeq idx op P (fun i => fun_ord_to_nat x0 F i.val) (List.finRange n) := by
  rw [eq_bigr_ord T n op idx (List.finRange n) P (fun_ord_to_nat x0 F) F]
  intro i _
  exact eq_fun_ord_to_nat n x0 F i

end Prosa.Classic.Util.Bigord
