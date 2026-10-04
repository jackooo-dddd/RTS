-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/find_seq.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 22)

import Prosa.Classic.Util.All

/-!
Finding the first element of a list that satisfies a predicate.

Representation notes:
* `Context {T : eqType}` is a carrier with `[DecidableEq T]`; the section variable `P : T -> bool` is a
  Boolean function, abstracted only by the declarations that use it (`findP`, `findP_FIFO`,
  `findP_in_seq`, `findP_notSome_in_seq`).
* MathComp's `find p s` (the index of the first element satisfying `p`, `size s` if none) is
  `List.findIdx p s`; `has p s` is `s.any p`; `uniq` is `Nodup`; `x \in l` is `x ∈ l`.
* Boolean predicates in proposition position are `= true`; `~ P x` is `¬ P x = true`; the Boolean
  `findP l != Some x` is `(!decide (findP P l = some x)) = true`.
-/

namespace Prosa.Classic.Util.FindSeq

universe u

def findP {T : Type u} [DecidableEq T] (P : T → Bool) : List T → Option T
  | [] => none
  | x :: s => if P x then some x else findP P s

theorem findP_FIFO {T : Type u} [DecidableEq T] (P : T → Bool) :
    ∀ (l : List T) (x y : T),
      P y = true → y ∈ l → x ≠ y →
      findP P l = some x →
      List.findIdx (fun j => decide (j = x)) l < List.findIdx (fun j => decide (j = y)) l := by
  intro l x y PY YIN NEQ FIND
  induction l with
  | nil => simp at YIN
  | cons a l ih =>
    simp only [List.findIdx_cons]
    by_cases AX : a = x
    · subst AX
      have AY : a ≠ y := NEQ
      simp [AY]
    · by_cases AY : a = y
      · subst AY
        simp only [findP, PY, if_true] at FIND
        exact absurd (Option.some.inj FIND) AX
      · simp only [AX, AY, decide_false, cond_false]
        have YIN' : y ∈ l := by
          rcases List.mem_cons.mp YIN with h | h
          · exact absurd h.symm AY
          · exact h
        have FIND' : findP P l = some x := by
          simp only [findP] at FIND
          cases hPa : P a
          · simpa [hPa] using FIND
          · simp only [hPa, if_true] at FIND; exact absurd (Option.some.inj FIND) AX
        exact Nat.succ_lt_succ (ih YIN' FIND')

theorem find_uniql {T : Type u} [DecidableEq T] :
    ∀ (x : T) (l1 l2 : List T), (l1 ++ l2).Nodup → x ∈ l2 → ¬ x ∈ l1 := by
  intro x l1 l2 H H0 XIN
  exact List.disjoint_of_nodup_append H XIN H0

theorem find_uniq {T : Type u} [DecidableEq T] :
    ∀ (x : T) (l1 l2 : List T), (l1 ++ l2).Nodup → x ∈ l2 →
      l1.any (fun x' => decide (x' = x)) = false := by
  intro x l1 l2 H H0
  have := find_uniql x l1 l2 H H0
  simp only [List.any_eq_false, decide_eq_true_eq]
  intro x' hx' heq
  exact this (heq ▸ hx')

theorem findP_in_seq {T : Type u} [DecidableEq T] (P : T → Bool) :
    ∀ (l : List T) (x : T), findP P l = some x → P x = true ∧ x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; simp [findP] at h
  | cons a l ih =>
    intro x FIND
    simp only [findP] at FIND
    cases hPa : P a
    · simp only [hPa] at FIND
      obtain ⟨h1, h2⟩ := ih x (by simpa using FIND)
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩
    · simp only [hPa, if_true, Option.some.injEq] at FIND
      subst FIND
      exact ⟨hPa, List.mem_cons_self⟩

theorem findP_notSome_in_seq {T : Type u} [DecidableEq T] (P : T → Bool) :
    ∀ (l : List T) (x : T), (!decide (findP P l = some x)) = true → x ∈ l →
      ¬ P x = true ∨ ∃ y, findP P l = some y := by
  intro l
  induction l with
  | nil => intro x _ h; simp at h
  | cons a l ih =>
    intro x G IN
    cases hPa : P a
    · by_cases AX : a = x
      · subst AX; left; simp [hPa]
      · have XINL : x ∈ l := by
          rcases List.mem_cons.mp IN with h | h
          · exact absurd h.symm AX
          · exact h
        have G' : (!decide (findP P l = some x)) = true := by simpa [findP, hPa] using G
        rcases ih x G' XINL with h | ⟨y, hy⟩
        · exact Or.inl h
        · exact Or.inr ⟨y, by simp [findP, hPa, hy]⟩
    · exact Or.inr ⟨a, by simp [findP, hPa]⟩

end Prosa.Classic.Util.FindSeq
