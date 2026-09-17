-- Translated from: ../rt-proofs/util/supremum.v
import Mathlib.Data.List.Basic

namespace Prosa.Util.Supremum

section SelectSupremum

variable {T : Type _} [DecidableEq T]
variable (R : T → T → Bool)

def choose_superior (x : T) (maybe_y : Option T) : Option T :=
  match maybe_y with
  | some y => if R x y then some x else some y
  | none => some x

def supremum (s : List T) : Option T := s.foldr (choose_superior R) none

theorem supremum_unfold :
    ∀ head tail,
      supremum R (head :: tail) = choose_superior R head (supremum R tail) := by
  intros; rfl

theorem supremum_exists :
    ∀ x s, x ∈ s → supremum R s ≠ none := by
  intro x s hx
  induction s with
  | nil => simp at hx
  | cons a l _ =>
    simp only [supremum, List.foldr, choose_superior]
    match List.foldr (choose_superior R) none l with
    | none => simp
    | some b => simp; split <;> simp

theorem supremum_none :
    ∀ s, supremum R s = none → s = [] := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons a l _ =>
    simp only [supremum, List.foldr, choose_superior]
    intro h; revert h
    match List.foldr (choose_superior R) none l with
    | none => simp
    | some b => simp; split <;> simp

theorem supremum_in :
    ∀ x s,
      supremum R s = some x →
      x ∈ s := by
  intro x s
  induction s with
  | nil => simp [supremum, List.foldr]
  | cons a l ih =>
    simp only [supremum, List.foldr, choose_superior]
    simp only [List.mem_cons]
    match hsl : List.foldr (choose_superior R) none l with
    | none =>
      intro h; left; exact (Option.some.inj h).symm
    | some b =>
      intro h
      by_cases hR : R a b = true
      · simp [hR] at h; left; exact h.symm
      · have hR_false : R a b = false := by cases hb : R a b <;> simp_all
        simp [hR_false] at h; right
        exact ih (by simp [supremum]; rw [← h]; exact hsl)

variable (H_R_reflexive : ∀ x, R x x = true)
variable (H_R_total : ∀ x y, R x y || R y x = true)
variable (H_R_transitive : ∀ y x z, R x y = true → R y z = true → R x z = true)

include H_R_reflexive H_R_total H_R_transitive in
theorem supremum_spec :
    ∀ x s,
      supremum R s = some x →
      ∀ y,
        y ∈ s → R x y = true := by
  intro z s
  induction s generalizing z with
  | nil =>
    intro h
    unfold supremum at h; simp only [List.foldr] at h
    exact nomatch h
  | cons a l ih =>
    intro hsup y hy
    rw [List.mem_cons] at hy
    have hsup_eq : supremum R (a :: l) = choose_superior R a (supremum R l) :=
      supremum_unfold R a l
    rw [hsup_eq] at hsup
    cases hsl : supremum R l with
    | none =>
      have hl_nil : l = [] := supremum_none R l hsl
      subst hl_nil
      rw [hsl] at hsup
      -- hsup : choose_superior R a none = some z
      -- choose_superior R a none = some a
      have : choose_superior R a none = some a := rfl
      rw [this] at hsup
      have haz : a = z := Option.some.inj hsup
      rcases hy with rfl | h
      · rw [← haz]; exact H_R_reflexive _
      · exact nomatch h
    | some b =>
      rw [hsl] at hsup
      have hsup2 : (if R a b then some a else some b) = some z := by
        rwa [choose_superior] at hsup
      by_cases hRab : R a b = true
      · rw [if_pos (show R a b = true from hRab)] at hsup2
        have haz : a = z := Option.some.inj hsup2
        rcases hy with rfl | hy_in_l
        · rw [← haz]; exact H_R_reflexive _
        · have hRby : R b y = true := ih b hsl y hy_in_l
          rw [← haz]; exact H_R_transitive b _ y hRab hRby
      · have hRab_false : R a b = false := by
          cases h : R a b with
          | true => exact absurd h hRab
          | false => rfl
        rw [if_neg (show ¬(R a b = true) from hRab)] at hsup2
        have hbz : b = z := Option.some.inj hsup2
        rcases hy with heq | hy_in_l
        · rw [← hbz, heq]
          have htot := H_R_total a b
          rw [hRab_false] at htot
          -- htot : (false || decide (R b a = true)) = true
          have : decide (R b a = true) = true := by
            rw [Bool.false_or] at htot; exact htot
          rwa [decide_eq_true_eq] at this
        · rw [← hbz]
          exact ih b hsl y hy_in_l

end SelectSupremum

end Prosa.Util.Supremum
