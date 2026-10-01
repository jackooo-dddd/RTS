-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/counting.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 14)

import Prosa.Classic.Util.OrdQuantifier
import Mathlib.Data.List.Perm.Subperm

/-!
Additional lemmas about counting.

Representation notes: `count P l` is `List.countP P l`; `{subset l1 <= l2}` is
`∀ x, x ∈ l1 → x ∈ l2`; Boolean predicates in proposition position are
`P x = true`; `[exists x in 'I_n, P y x]` is `(List.finRange n).any (P y)` (as
in `ord_quantifier`), and `widen_ord (leqnSn n)` / `ord_max` are
`Fin.castSucc` / `Fin.last n`.
-/

namespace Prosa.Classic.Util.Counting

open Prosa.Classic.Util.OrdQuantifier

universe u

theorem count_or :
    ∀ (T : Type u) [DecidableEq T] (l : List T) (P Q : T → Bool),
      l.countP (fun x => P x || Q x) ≤ l.countP P + l.countP Q := by
  intro T _ l P Q
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.countP_cons]
      cases P a <;> cases Q a <;> simp <;> omega

theorem sub_in_count :
    ∀ (T : Type u) [DecidableEq T] (l : List T) (P1 P2 : T → Bool),
      (∀ x, x ∈ l → P1 x = true → P2 x = true) →
      l.countP P1 ≤ l.countP P2 := by
  intro T _ l P1 P2 SUB
  induction l with
  | nil => simp
  | cons a l ih =>
      have ih' := ih (fun x hx h => SUB x (List.mem_cons_of_mem _ hx) h)
      simp only [List.countP_cons]
      by_cases h1 : P1 a = true
      · have h2 := SUB a List.mem_cons_self h1
        simp [h1, h2]; omega
      · have h1' : P1 a = false := by simpa using h1
        rw [h1']
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.le_trans ih' (Nat.le_add_right _ _)

theorem count_sub_uniqr :
    ∀ (T : Type u) [DecidableEq T] (l1 l2 : List T) (P : T → Bool),
      l1.Nodup →
      (∀ x, x ∈ l1 → x ∈ l2) →
      l1.countP P ≤ l2.countP P := by
  intro T _ l1 l2 P UNIQ SUB
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  apply List.Subperm.length_le
  apply List.subperm_of_subset (UNIQ.filter _)
  intro x hx
  rw [List.mem_filter] at hx ⊢
  exact ⟨SUB x hx.1, hx.2⟩

theorem count_pred_inj :
    ∀ (T : Type u) [DecidableEq T] (l : List T) (P : T → Bool),
      l.Nodup →
      (∀ x1 x2, P x1 = true → P x2 = true → x1 = x2) →
      l.countP P ≤ 1 := by
  intro T _ l P UNIQ INJ
  rw [List.countP_eq_length_filter]
  cases h : l.filter P with
  | nil => simp
  | cons x rest =>
      have hx : P x = true := (List.mem_filter.mp (h ▸ List.mem_cons_self)).2
      have hnd : (x :: rest).Nodup := h ▸ UNIQ.filter P
      have hsub : x :: rest ⊆ [x] := by
        intro y hy
        have hy' : P y = true := (List.mem_filter.mp (h ▸ hy)).2
        simp [INJ y x hy' hx]
      simpa using (List.subperm_of_subset hnd hsub).length_le

theorem count_exists :
    ∀ (T : Type u) [DecidableEq T] (l : List T) (n : Nat) (P : T → Fin n → Bool),
      l.Nodup →
      (∀ y x1 x2, P x1 y = true → P x2 y = true → x1 = x2) →
      l.countP (fun y => (List.finRange n).any (P y)) ≤ n := by
  intro T _ l n
  induction n with
  | zero =>
      intro P _ _
      simp [List.countP_eq_zero]
  | succ n ih =>
      intro P UNIQ INJ
      have hfun : (fun y => (List.finRange (n + 1)).any (P y)) =
          (fun y => (List.finRange n).any (fun x => P y (Fin.castSucc x)) ||
            P y (Fin.last n)) := by
        funext y
        exact exists_recr n (P y)
      rw [hfun]
      calc l.countP (fun y => (List.finRange n).any (fun x => P y (Fin.castSucc x)) ||
              P y (Fin.last n))
          ≤ l.countP (fun y => (List.finRange n).any (fun x => P y (Fin.castSucc x))) +
              l.countP (fun y => P y (Fin.last n)) := count_or T l _ _
        _ ≤ n + 1 := by
          apply Nat.add_le_add
          · exact ih (fun y x => P y (Fin.castSucc x)) UNIQ
              (fun y x1 x2 h1 h2 => INJ (Fin.castSucc y) x1 x2 h1 h2)
          · exact count_pred_inj T l _ UNIQ
              (fun x1 x2 h1 h2 => INJ (Fin.last n) x1 x2 h1 h2)

end Prosa.Classic.Util.Counting
