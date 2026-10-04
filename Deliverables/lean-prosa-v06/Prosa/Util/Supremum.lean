-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/supremum.v

import Mathlib.Data.List.Basic

namespace Prosa.Util.Supremum

universe u

variable {T : Type u} [DecidableEq T]

def choose_superior (R : T → T → Bool) (x : T)
    (maybeY : Option T) : Option T :=
  match maybeY with
  | some y => if R x y then some x else some y
  | none => some x

def supremum (R : T → T → Bool) (s : List T) : Option T :=
  s.foldr (choose_superior R) none

theorem supremum_unfold (R : T → T → Bool) (head : T) (tail : List T) :
    supremum R (head :: tail) = choose_superior R head (supremum R tail) := by
  rfl

theorem supremum_exists (R : T → T → Bool) :
    ∀ x s, x ∈ s → supremum R s ≠ none := by
  intro x s hx
  induction s with
  | nil => simp at hx
  | cons a tail _ =>
    simp only [supremum, List.foldr, choose_superior]
    match List.foldr (choose_superior R) none tail with
    | none => simp
    | some b => simp; split <;> simp

theorem supremum_none (R : T → T → Bool) :
    ∀ s, supremum R s = none → s = [] := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons a tail _ =>
    simp only [supremum, List.foldr, choose_superior]
    intro h
    revert h
    match List.foldr (choose_superior R) none tail with
    | none => simp
    | some b => simp; split <;> simp

theorem supremum_in (R : T → T → Bool) :
    ∀ x s, supremum R s = some x → x ∈ s := by
  intro x s
  induction s with
  | nil => simp [supremum]
  | cons a tail ih =>
      simp only [supremum, List.foldr, choose_superior, List.mem_cons]
      cases htail : List.foldr (choose_superior R) none tail with
      | none =>
          intro h
          left
          exact (Option.some.inj h).symm
      | some b =>
          by_cases hR : R a b = true
          · simp [hR] at htail ⊢
            intro h
            left
            exact h.symm
          · have hRfalse : R a b = false := by cases h : R a b <;> simp_all
            simp [hRfalse] at htail ⊢
            intro h
            right
            exact ih (by simp [supremum]; rw [← h]; exact htail)

theorem supremum_spec (R : T → T → Bool)
    (hRefl : ∀ x, R x x = true)
    (hTotal : ∀ x y, (R x y || R y x) = true)
    (hTrans : ∀ x y z, R x y = true → R y z = true → R x z = true) :
    ∀ x s, supremum R s = some x → ∀ y, y ∈ s → R x y = true := by
  intro z s
  induction s generalizing z with
  | nil =>
      intro h
      unfold supremum at h
      simp only [List.foldr] at h
      exact nomatch h
  | cons a tail ih =>
      intro hSup y hy
      rw [supremum_unfold] at hSup
      cases hTail : supremum R tail with
      | none =>
          have hNil : tail = [] := supremum_none R tail hTail
          subst tail
          rw [hTail] at hSup
          have hChoose : choose_superior R a none = some a := rfl
          rw [hChoose] at hSup
          have haz : a = z := Option.some.inj hSup
          have hya : y = a := by simpa using hy
          subst y
          rw [← haz]
          exact hRefl _
      | some b =>
          rw [hTail] at hSup
          have hSup' : (if R a b then some a else some b) = some z := by
            rwa [choose_superior] at hSup
          rw [List.mem_cons] at hy
          rcases hy with rfl | hyTail
          · by_cases hRab : R y b = true
            · rw [if_pos hRab] at hSup'
              have haz : y = z := Option.some.inj hSup'
              rw [← haz]
              exact hRefl _
            · have hRabFalse : R y b = false := by cases h : R y b <;> simp_all
              rw [if_neg hRab] at hSup'
              have hbz : b = z := Option.some.inj hSup'
              rw [← hbz]
              have hTot := hTotal y b
              rw [hRabFalse, Bool.false_or] at hTot
              exact hTot
          · have hRby : R b y = true := ih b hTail y hyTail
            by_cases hRab : R a b = true
            · rw [if_pos hRab] at hSup'
              have haz : a = z := Option.some.inj hSup'
              rw [← haz]
              exact hTrans a b y hRab hRby
            · rw [if_neg hRab] at hSup'
              have hbz : b = z := Option.some.inj hSup'
              rw [← hbz]
              exact hRby

end Prosa.Util.Supremum
