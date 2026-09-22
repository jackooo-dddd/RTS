-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/minmax.v

import Mathlib.Tactic
import Prosa.Util.List
import Prosa.Util.Nat
import Prosa.Util.Notation
import Prosa.Util.Setoid

namespace Prosa.Util.Minmax

universe u

/-- LEAN_HELPER: the source conditional `maxn` big operator over an ordered
    sequence, retaining the source Boolean predicate and zero identity. -/
def bigMaxListCond {X : Type u} (xs : List X) (P : X → Bool)
    (F : X → Nat) : Nat :=
  xs.foldr (fun x current => if P x then Nat.max (F x) current else current) 0

/-- LEAN_HELPER: the same conditional maximum over the canonical enumeration
    `0, ..., n - 1` used by MathComp ordinals. -/
def bigMaxNatRange : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, P =>
      if P n then Nat.max (bigMaxNatRange n P) n
      else bigMaxNatRange n P

private theorem bigMaxNatRange_le (n : Nat) (P : Nat → Bool) :
    bigMaxNatRange n P ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [bigMaxNatRange]
      by_cases hPn : P n = true
      · rw [if_pos hPn]
        exact (Nat.max_le).2 ⟨le_trans ih (Nat.le_succ n), Nat.le_succ n⟩
      · rw [if_neg hPn]
        exact le_trans ih (Nat.le_succ n)

private theorem bigMaxNatRange_succ_le (n : Nat) (P : Nat → Bool) :
    bigMaxNatRange (n + 1) P ≤ n := by
  simp only [bigMaxNatRange]
  by_cases hPn : P n = true
  · rw [if_pos hPn]
    exact (Nat.max_le).2 ⟨bigMaxNatRange_le n P, le_rfl⟩
  · rw [if_neg hPn]
    exact bigMaxNatRange_le n P

private theorem bigMaxNatRange_pred_of_exists (n : Nat) (P : Nat → Bool)
    (hExists : ∃ i, i < n ∧ P i = true) :
    P (bigMaxNatRange n P) = true := by
  induction n with
  | zero =>
      obtain ⟨i, hi, _⟩ := hExists
      omega
  | succ n ih =>
      by_cases hPn : P n = true
      · have hMax : Nat.max (bigMaxNatRange n P) n = n :=
          Nat.max_eq_right (bigMaxNatRange_le n P)
        simp [bigMaxNatRange, hPn, hMax]
      · have hEarlier : ∃ i, i < n ∧ P i = true := by
          obtain ⟨i, hi, hPi⟩ := hExists
          refine ⟨i, ?_, hPi⟩
          have hin : i ≤ n := Nat.le_of_lt_succ hi
          exact Nat.lt_of_le_of_ne hin (fun hEq => hPn (hEq ▸ hPi))
        simpa [bigMaxNatRange, hPn] using ih hEarlier

private theorem bigMaxListCond_eq_zero_of_all_false {X : Type u}
    (xs : List X) (P : X → Bool) (F : X → Nat)
    (h : ∀ x, x ∈ xs → P x = false) : bigMaxListCond xs P F = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hPx : P x = false := h x (by simp)
      have hTail : ∀ y, y ∈ xs → P y = false := by
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)
      change (if P x = true then Nat.max (F x) (bigMaxListCond xs P F)
        else bigMaxListCond xs P F) = 0
      simp [hPx, ih hTail]

private theorem bigMaxListCond_witness {X : Type u} [DecidableEq X]
    {xs : List X} {P : X → Bool} (F : X → Nat)
    (h : xs.any P = true) :
    ∃ x, x ∈ xs ∧ P x = true ∧ F x = bigMaxListCond xs P F := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      cases hPa : P a with
      | false =>
          have hTail : xs.any P = true := by simpa [List.any_cons, hPa] using h
          obtain ⟨x, hx, hPx, hEq⟩ := ih hTail
          exact ⟨x, List.mem_cons_of_mem a hx, hPx, by
            simpa [bigMaxListCond, hPa] using hEq⟩
      | true =>
          cases hTail : xs.any P with
          | false =>
              have hAllFalse : ∀ x, x ∈ xs → P x = false := by
                intro x hx
                have hNot := (List.any_eq_false.mp hTail) x hx
                cases hPx : P x with
                | false => rfl
                | true => exact False.elim (hNot hPx)
              have hZero := bigMaxListCond_eq_zero_of_all_false xs P F hAllFalse
              exact ⟨a, by simp, hPa, by
                change F a = (if P a = true then
                  Nat.max (F a) (bigMaxListCond xs P F)
                  else bigMaxListCond xs P F)
                simp [hPa, hZero]⟩
          | true =>
              obtain ⟨x, hx, hPx, hEq⟩ := ih hTail
              by_cases hLe : bigMaxListCond xs P F ≤ F a
              · exact ⟨a, by simp, hPa, by
                  change F a = (if P a = true then
                    Nat.max (F a) (bigMaxListCond xs P F)
                    else bigMaxListCond xs P F)
                  simp [hPa, Nat.max_eq_left hLe]⟩
              · have hFa : F a ≤ bigMaxListCond xs P F :=
                  Nat.le_of_lt (Nat.lt_of_not_ge hLe)
                exact ⟨x, List.mem_cons_of_mem a hx, hPx, by
                  change F x = (if P a = true then
                    Nat.max (F a) (bigMaxListCond xs P F)
                    else bigMaxListCond xs P F)
                  simpa [hPa, Nat.max_eq_right hFa] using hEq⟩

theorem leq_bigmax_cond_seq {X : Type u} [DecidableEq X]
    (F : X → Nat) (P : X → Bool) (xs : List X) (x : X)
    (hMem : x ∈ xs) (hPx : P x = true) :
    F x ≤ bigMaxListCond xs P F := by
  induction xs with
  | nil => simp at hMem
  | cons a xs ih =>
      rcases List.mem_cons.mp hMem with rfl | hTail
      · simp [bigMaxListCond, hPx]
      · cases hPa : P a with
        | false => simpa [bigMaxListCond, hPa] using ih hTail
        | true =>
            simpa [bigMaxListCond, hPa] using
              le_trans (ih hTail) (Nat.le_max_right (F a) _)

theorem leq_bigmax_sup {X : Type u} [DecidableEq X]
    (P : X → Bool) (F : X → Nat) (xs : List X) (n : Nat)
    (h : ∃ x, x ∈ xs ∧ P x = true ∧ n ≤ F x) :
    n ≤ bigMaxListCond xs P F := by
  obtain ⟨x, hx, hPx, hLe⟩ := h
  exact le_trans hLe (leq_bigmax_cond_seq F P xs x hx hPx)

theorem bigmax_leq_seqP {X : Type u} [DecidableEq X]
    (F : X → Nat) (P : X → Bool) (xs : List X) (m : Nat) :
    bigMaxListCond xs P F ≤ m ↔
      ∀ x, x ∈ xs → P x = true → F x ≤ m := by
  constructor
  · intro hMax x hx hPx
    exact le_trans (leq_bigmax_cond_seq F P xs x hx hPx) hMax
  · intro hAll
    induction xs with
    | nil => simp [bigMaxListCond]
    | cons a xs ih =>
        cases hPa : P a with
        | false =>
            simp only [bigMaxListCond, List.foldr_cons, hPa, Bool.false_eq_true,
              ↓reduceIte]
            apply ih
            intro x hx hPx
            exact hAll x (List.mem_cons_of_mem a hx) hPx
        | true =>
            simp only [bigMaxListCond, List.foldr_cons, hPa, if_pos]
            apply (Nat.max_le).2
            constructor
            · exact hAll a (by simp) hPa
            · apply ih
              intro x hx hPx
              exact hAll x (List.mem_cons_of_mem a hx) hPx

theorem leq_big_max {X : Type u} [DecidableEq X]
    (F₁ F₂ : X → Nat) (P : X → Bool) (xs : List X)
    (hPointwise : ∀ x, x ∈ xs → P x = true → F₁ x ≤ F₂ x) :
    bigMaxListCond xs P F₁ ≤ bigMaxListCond xs P F₂ := by
  rw [bigmax_leq_seqP]
  intro x hx hPx
  exact le_trans (hPointwise x hx hPx)
    (leq_bigmax_cond_seq F₂ P xs x hx hPx)

theorem bigmax_ord_ltn_identity (n : Nat) (hPos : n > 0) :
    bigMaxNatRange n (fun _ => true) < n := by
  cases n with
  | zero => omega
  | succ n => exact Nat.lt_succ_of_le (bigMaxNatRange_succ_le n (fun _ => true))

theorem bigmax_ltn_ord (n : Nat) (P : Nat → Bool) (i₀ : Fin n)
    (_hPi₀ : P i₀.val = true) :
    bigMaxNatRange n P < n := by
  cases n with
  | zero => exact Fin.elim0 i₀
  | succ n => exact Nat.lt_succ_of_le (bigMaxNatRange_succ_le n P)

theorem bigmax_pred (n : Nat) (P : Nat → Bool) (i₀ : Fin n)
    (hPi₀ : P i₀.val = true) :
    P (bigMaxNatRange n P) = true := by
  exact bigMaxNatRange_pred_of_exists n P ⟨i₀.val, i₀.isLt, hPi₀⟩

theorem bigmax_witness {X : Type u} [DecidableEq X]
    {xs : List X} {P : X → Bool} (F : X → Nat)
    (hHas : xs.any P = true) :
    ∃ x, x ∈ xs ∧ P x = true ∧ F x = bigMaxListCond xs P F :=
  bigMaxListCond_witness F hHas

theorem bigmax_witness_diff {X : Type u} [DecidableEq X]
    {xs : List X} {P₁ P₂ : X → Bool} {F : X → Nat}
    (hLt : bigMaxListCond xs P₁ F < bigMaxListCond xs P₂ F) :
    ∃ x, x ∈ xs ∧ P₁ x = false ∧ P₂ x = true := by
  cases hAny₂ : xs.any P₂ with
  | false =>
      have hAllFalse : ∀ x, x ∈ xs → P₂ x = false := by
        intro x hx
        have hNot := (List.any_eq_false.mp hAny₂) x hx
        cases hPx : P₂ x with
        | false => rfl
        | true => exact False.elim (hNot hPx)
      have hZero := bigMaxListCond_eq_zero_of_all_false xs P₂ F hAllFalse
      omega
  | true =>
      obtain ⟨x, hx, hP₂, hEq⟩ := bigMaxListCond_witness F hAny₂
      cases hP₁ : P₁ x with
      | false => exact ⟨x, hx, hP₁, hP₂⟩
      | true =>
          have hLe := leq_bigmax_cond_seq F P₁ xs x hx hP₁
          omega

theorem bigmax_subset {X : Type u} [DecidableEq X]
    {xs : List X} {P₁ P₂ : X → Bool} {F : X → Nat}
    (hImpl : ∀ x, x ∈ xs → P₁ x = true → P₂ x = true) :
    bigMaxListCond xs P₁ F ≤ bigMaxListCond xs P₂ F := by
  rw [bigmax_leq_seqP]
  intro x hx hP₁
  exact leq_bigmax_cond_seq F P₂ xs x hx (hImpl x hx hP₁)

end Prosa.Util.Minmax
