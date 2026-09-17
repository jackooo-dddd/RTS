-- Translated from: ../rt-proofs/classic/util/bigord.v
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Bigord

section BigOrdFunOrd

def fun_ord_to_nat {n : ℕ} {T : Type _} (x0 : T) (f : Fin n → T) : ℕ → T :=
  fun x => if h : x < n then f ⟨x, h⟩ else x0

theorem eq_fun_ord_to_nat (n : ℕ) {T : Type _} (x0 : T) (f : Fin n → T) (x : Fin n) :
    fun_ord_to_nat x0 f x.val = f x := by
  unfold fun_ord_to_nat
  rw [dif_pos x.isLt]

theorem eq_bigr_ord {T : Type _} {n : ℕ} (op : T → T → T) (idx : T)
    (r : List (Fin n)) (P : Fin n → Bool)
    (F1 : ℕ → T) (F2 : Fin n → T)
    (h : ∀ i : Fin n, P i = true → F1 i.val = F2 i) :
    List.foldl (fun acc i => if P i then op acc (F1 i.val) else acc) idx r =
    List.foldl (fun acc i => if P i then op acc (F2 i) else acc) idx r := by
  induction r generalizing idx with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    cases hPa : P a with
    | true =>
      simp only [ite_true]
      rw [h a hPa]
      exact ih _
    | false =>
      exact ih _

theorem big_mkord_ord {T : Type _} {n : ℕ} {op : T → T → T} {idx : T}
    (x0 : T) (P : Fin n → Bool) (F : Fin n → T) :
    List.foldl (fun acc i => if P i then op acc (F i) else acc) idx (List.finRange n) =
    List.foldl (fun acc i => if P i then op acc (fun_ord_to_nat x0 F i.val) else acc) idx (List.finRange n) := by
  symm
  exact eq_bigr_ord op idx (List.finRange n) P (fun_ord_to_nat x0 F) F (fun i hP => eq_fun_ord_to_nat n x0 F i)

end BigOrdFunOrd

end Prosa.Classic.Util.Bigord
