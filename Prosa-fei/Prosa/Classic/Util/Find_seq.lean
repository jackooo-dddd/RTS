-- Translated from: ../rt-proofs/classic/util/find_seq.v
import Mathlib

namespace Prosa.Classic.Util.Find_seq

open List

section find_seq

  variable {T : Type _} [DecidableEq T]
  variable (P : T → Bool)

  def findP : List T → Option T
    | [] => none
    | x :: s => if P x then some x else findP s

  theorem findP_FIFO (l : List T) (x y : T)
      (hPy : P y = true) (hyin : y ∈ l) (hneq : x ≠ y)
      (hfind : findP P l = some x) :
      l.idxOf x < l.idxOf y := by
    induction l with
    | nil => simp at hyin
    | cons a t ih =>
      rw [List.mem_cons] at hyin
      unfold findP at hfind
      split_ifs at hfind with hPa
      · -- P a is true, so findP returns a, meaning a = x
        have hxa : a = x := Option.some.inj hfind.symm |>.symm
        subst hxa
        rw [List.idxOf_cons_eq _ rfl, List.idxOf_cons_ne _ hneq]
        omega
      · -- P a is false
        by_cases hax : a = x
        · subst hax
          rw [List.idxOf_cons_eq _ rfl, List.idxOf_cons_ne _ hneq]
          omega
        · by_cases hay : a = y
          · subst hay
            simp [hPy] at hPa
          · rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay]
            simp only [Nat.succ_lt_succ_iff]
            rcases hyin with rfl | hyin
            · exact absurd rfl hay
            · exact ih hyin hfind

  theorem find_uniql (x : T) (l1 l2 : List T)
      (huniq : (l1 ++ l2).Nodup) (hx : x ∈ l2) :
      x ∉ l1 := by
    intro hx1
    exact List.disjoint_of_nodup_append huniq hx1 hx

  theorem find_uniq (x : T) (l1 l2 : List T)
      (huniq : (l1 ++ l2).Nodup) (hx : x ∈ l2) :
      l1.any (fun x' => decide (x' = x)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨x', hx', hd⟩ := h
    simp only [decide_eq_true_eq] at hd
    exact absurd (hd ▸ hx') (find_uniql x l1 l2 huniq hx)

  theorem findP_in_seq (l : List T) (x : T)
      (hfind : findP P l = some x) :
      P x = true ∧ x ∈ l := by
    induction l with
    | nil => simp [findP] at hfind
    | cons a t ih =>
      unfold findP at hfind
      split_ifs at hfind with hPa
      · obtain rfl := Option.some.inj hfind
        exact ⟨hPa, List.mem_cons_self⟩
      · exact ⟨(ih hfind).1, List.mem_cons_of_mem _ (ih hfind).2⟩

  theorem findP_notSome_in_seq (l : List T) (x : T)
      (hnfind : findP P l ≠ some x) (hin : x ∈ l) :
      ¬(P x = true) ∨ ∃ y, findP P l = some y := by
    induction l with
    | nil => simp at hin
    | cons a t ih =>
      have hfp : findP P (a :: t) = if P a then some a else findP P t := rfl
      rw [hfp] at hnfind ⊢
      by_cases hPa : P a = true
      · rw [if_pos hPa]
        right; exact ⟨a, rfl⟩
      · push_neg at hPa
        have hPaf : P a = false := Bool.eq_false_iff.mpr hPa
        rw [if_neg (by rw [hPaf]; simp)] at hnfind ⊢
        rw [List.mem_cons] at hin
        rcases hin with rfl | hin
        · left; intro h; rw [h] at hPaf; simp at hPaf
        · rcases ih hnfind hin with h | ⟨y, hy⟩
          · left; exact h
          · right; exact ⟨y, hy⟩

end find_seq

end Prosa.Classic.Util.Find_seq
