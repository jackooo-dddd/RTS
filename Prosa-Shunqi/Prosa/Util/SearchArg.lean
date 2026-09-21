-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/search_arg.v

import Mathlib.Tactic
import Mathlib.Data.Nat.Find
import Prosa.Util.Tactics

namespace Prosa.Util.SearchArg

/-- Either no natural in `[t1, t2)` satisfies `P`, or there is a least
satisfying natural (also least among all satisfying naturals at least `t1`). -/
theorem earliest_pred_element_exists_case
    (P : Nat → Bool) (t1 t2 : Nat) :
    (∀ t, t1 ≤ t ∧ t < t2 → P t = false) ∨
      ∃ t, (t1 ≤ t ∧ t < t2) ∧ P t = true ∧
        ∀ t', t1 ≤ t' → P t' = true → t ≤ t' := by
  by_cases hex : ∃ t, (t1 ≤ t ∧ t < t2) ∧ P t = true
  · right
    rcases hex with ⟨w, hw, hPw⟩
    let Q : Nat → Prop := fun n => t1 ≤ n ∧ P n = true
    have hQ : ∃ n, Q n := ⟨w, hw.1, hPw⟩
    let t := Nat.find hQ
    have htQ : Q t := Nat.find_spec hQ
    have htw : t ≤ w := Nat.find_min' hQ ⟨hw.1, hPw⟩
    exact ⟨t, ⟨htQ.1, lt_of_le_of_lt htw hw.2⟩, htQ.2,
      fun t' ht1 hPt' => Nat.find_min' hQ ⟨ht1, hPt'⟩⟩
  · left
    intro t ht
    cases hPt : P t with
    | false => rfl
    | true => exact False.elim (hex ⟨t, ht, hPt⟩)

section ArgSearch

variable {T : Type _}
variable (f : Nat → T)
variable (P : T → Bool)
variable (R : T → T → Bool)

/-- Search `[a,b)` from right to left, retaining the `R`-extremal argument
whose image under `f` satisfies `P`. -/
def search_arg (a b : Nat) : Option Nat :=
  if a < b then
    match b with
    | 0 => none
    | b' + 1 =>
      match search_arg a b' with
      | none => if P (f b') then some b' else none
      | some x => if P (f b') && R (f b') (f x) then some b' else some x
  else none

private theorem search_arg_none_not_true (a b : Nat) :
    search_arg f P R a b = none ↔
      ∀ x, a ≤ x ∧ x < b → ¬ (P (f x) = true) := by
  constructor
  · induction b with
    | zero => intro _ x ⟨_, hxb⟩; omega
    | succ n ih =>
      simp only [search_arg]
      by_cases h : a < n + 1
      · simp only [if_pos h]
        cases hsa : search_arg f P R a n with
        | none =>
          simp only
          split_ifs with hp
          · simp
          · intro _ x ⟨hax, hxn⟩
            by_cases hxn' : x < n
            · exact ih hsa x ⟨hax, hxn'⟩
            · have : x = n := by omega
              rw [this]
              exact hp
        | some q =>
          simp only
          split_ifs <;> simp
      · simp only [if_neg h]
        intro _ x ⟨hax, hxn⟩
        omega
  · induction b with
    | zero =>
      intro _
      simp only [search_arg]
      split_ifs <;> rfl
    | succ n ih =>
      intro hnot
      simp only [search_arg]
      by_cases h : a < n + 1
      · simp only [if_pos h]
        have hrec : search_arg f P R a n = none := by
          apply ih
          intro x ⟨hax, hxn⟩
          exact hnot x ⟨hax, by omega⟩
        rw [hrec]
        simp only
        have hnotpn : ¬ (P (f n) = true) := hnot n ⟨by omega, by omega⟩
        simp [show P (f n) ≠ true from hnotpn]
      · simp only [if_neg h]

theorem search_arg_none (a b : Nat) :
    search_arg f P R a b = none ↔
      ∀ x, a ≤ x ∧ x < b → P (f x) = false := by
  simpa only [Bool.eq_false_iff] using search_arg_none_not_true f P R a b

theorem search_arg_not_none (a b : Nat) :
    (∃ x, (a ≤ x ∧ x < b) ∧ P (f x) = true) →
      ∃ y, search_arg f P R a b = some y := by
  intro ⟨x, hrange, hpx⟩
  by_contra h
  push_neg at h
  have hnone : search_arg f P R a b = none := by
    cases hsab : search_arg f P R a b with
    | none => rfl
    | some y => exact absurd hsab (h y)
  rw [search_arg_none] at hnone
  have := hnone x hrange
  simp_all

theorem search_arg_pred (a b x : Nat) :
    search_arg f P R a b = some x → P (f x) = true := by
  induction b generalizing x with
  | zero =>
    simp only [search_arg]
    split_ifs <;> simp
  | succ n ih =>
    simp only [search_arg]
    by_cases h : a < n + 1
    · simp only [if_pos h]
      cases hsa : search_arg f P R a n with
      | none =>
        simp only
        split_ifs with hp
        · intro hx
          have := Option.some.inj hx
          subst this
          exact hp
        · simp
      | some q =>
        simp only
        split_ifs with hpq
        · intro hx
          have := Option.some.inj hx
          subst this
          exact (Bool.and_eq_true_iff.mp hpq).1
        · intro hx
          have := Option.some.inj hx
          subst this
          exact ih q hsa
    · simp only [if_neg h]
      simp

theorem search_arg_in_range (a b x : Nat) :
    search_arg f P R a b = some x → a ≤ x ∧ x < b := by
  induction b generalizing x with
  | zero =>
    simp only [search_arg]
    split_ifs <;> simp
  | succ n ih =>
    simp only [search_arg]
    by_cases h : a < n + 1
    · simp only [if_pos h]
      cases hsa : search_arg f P R a n with
      | none =>
        simp only
        split_ifs with hp
        · intro hx
          have := Option.some.inj hx
          subst this
          constructor <;> omega
        · simp
      | some q =>
        simp only
        split_ifs with hpq
        · intro hx
          have := Option.some.inj hx
          subst this
          constructor <;> omega
        · intro hx
          have := Option.some.inj hx
          subst this
          have hiq := ih q hsa
          exact ⟨hiq.1, by omega⟩
    · simp only [if_neg h]
      simp

variable (R_reflexive : ∀ x, R x x = true)
variable (R_transitive : ∀ x y z, R x y = true → R y z = true → R x z = true)
variable (R_total : ∀ x y, R x y = true ∨ R y x = true)

include R_reflexive R_transitive R_total in
theorem search_arg_extremum (a b x : Nat) :
    search_arg f P R a b = some x →
      ∀ y, a ≤ y ∧ y < b → P (f y) = true → R (f x) (f y) = true := by
  induction b generalizing x with
  | zero =>
    simp only [search_arg]
    intro h
    exact absurd h (by split_ifs <;> exact fun h => nomatch h)
  | succ n ih =>
    simp only [search_arg]
    by_cases hab : a < n + 1
    · simp only [if_pos hab]
      cases hsa : search_arg f P R a n with
      | none =>
        simp only
        by_cases hp : P (f n) = true
        · simp only [if_pos hp]
          intro hx y ⟨hay, hpfy⟩
          have heq := Option.some.inj hx
          subst heq
          intro hpfy_val
          by_cases hyn : y < n
          · exfalso
            rw [search_arg_none] at hsa
            have hfalse := hsa y ⟨hay, hyn⟩
            simp_all
          · have hyn_eq : y = n := by omega
            rw [hyn_eq]
            exact R_reflexive (f n)
        · simp only [if_neg hp]
          intro h
          exact absurd h (fun h => nomatch h)
      | some q =>
        simp only
        by_cases hpq : (P (f n) && R (f n) (f q)) = true
        · simp only [if_pos hpq]
          intro hx y ⟨hay, hpfy⟩
          have heq := Option.some.inj hx
          subst heq
          intro hpfy_val
          have hpn := (Bool.and_eq_true_iff.mp hpq).1
          have hrq := (Bool.and_eq_true_iff.mp hpq).2
          by_cases hyn : y < n
          · have hiq := ih q hsa y ⟨hay, hyn⟩ hpfy_val
            exact R_transitive _ _ _ hrq hiq
          · have hyn_eq : y = n := by omega
            rw [hyn_eq]
            exact R_reflexive (f n)
        · simp only [if_neg hpq]
          intro hx y ⟨hay, hpfy⟩
          have heq := Option.some.inj hx
          subst heq
          intro hpfy_val
          by_cases hyn : y < n
          · exact ih q hsa y ⟨hay, hyn⟩ hpfy_val
          · have hyn_eq : y = n := by omega
            have hpn : P (f n) = true := by rw [← hyn_eq]; exact hpfy_val
            have hnotR : ¬ (R (f n) (f q) = true) := by
              intro hr
              exact hpq (Bool.and_eq_true_iff.mpr ⟨hpn, hr⟩)
            rw [hyn_eq]
            cases R_total (f q) (f n) with
            | inl h => exact h
            | inr h => exact absurd h hnotR
    · simp only [if_neg hab]
      intro h
      exact absurd h (fun h => nomatch h)

end ArgSearch

theorem prop_on_ex_minn
    (P : Nat → Prop) (pred : Nat → Bool)
    (ex : ∃ n, pred n = true) :
    P (Nat.find ex) →
      ∃ n, P n ∧ pred n = true ∧ ∀ n', pred n' = true → n ≤ n' := by
  intro hP
  exact ⟨Nat.find ex, hP, Nat.find_spec ex,
    fun n' hn' => Nat.find_min' ex hn'⟩

end Prosa.Util.SearchArg
