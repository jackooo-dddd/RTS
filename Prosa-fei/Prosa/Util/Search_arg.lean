-- Translated from: ../rt-proofs/util/search_arg.v
import Mathlib.Tactic
import Mathlib.Data.Nat.Find
import Prosa.Util.Tactics

namespace Prosa.Util.Search_arg

section ArgSearch

variable {T : Type _}
variable (f : ℕ → T)
variable (P : T → Bool)
variable (R : T → T → Bool)

def search_arg (a b : ℕ) : Option ℕ :=
  if a < b then
    match b with
    | 0 => none
    | b' + 1 =>
      match search_arg a b' with
      | none => if P (f b') then some b' else none
      | some x => if P (f b') && R (f b') (f x) then some b' else some x
  else none

theorem search_arg_none (a b : ℕ) :
    search_arg f P R a b = none ↔ ∀ x, a ≤ x ∧ x < b → ¬ (P (f x) = true) := by
  constructor
  · -- forward: search_arg = none → ∀ x, ...
    induction b with
    | zero => intro _ x ⟨_, hxb⟩; omega
    | succ n IH =>
      simp only [search_arg]
      by_cases h : a < n + 1
      · simp only [if_pos h]
        cases hsa : search_arg f P R a n with
        | none =>
          simp only []
          split_ifs with hp
          · simp
          · intro _ x ⟨hax, hxn⟩
            by_cases hxn' : x < n
            · exact IH hsa x ⟨hax, hxn'⟩
            · have : x = n := by omega
              rw [this]; exact hp
        | some q =>
          simp only []
          split_ifs <;> simp
      · simp only [if_neg h]
        intro _ x ⟨hax, hxn⟩; omega
  · -- backward: (∀ x, ...) → search_arg = none
    induction b with
    | zero =>
      intro _; simp only [search_arg]; split_ifs <;> rfl
    | succ n IH =>
      intro hnot
      simp only [search_arg]
      by_cases h : a < n + 1
      · simp only [if_pos h]
        have hrec : search_arg f P R a n = none := by
          apply IH
          intro x ⟨hax, hxn⟩
          exact hnot x ⟨hax, by omega⟩
        rw [hrec]; simp only []
        have hnotpn : ¬ (P (f n) = true) := hnot n ⟨by omega, by omega⟩
        simp [show P (f n) ≠ true from hnotpn]
      · simp only [if_neg h]

theorem search_arg_not_none (a b : ℕ) :
    (∃ x, (a ≤ x ∧ x < b) ∧ P (f x) = true) →
    ∃ y, search_arg f P R a b = some y := by
  intro ⟨x, ⟨hrange, hpx⟩⟩
  by_contra h
  push_neg at h
  have hnone : search_arg f P R a b = none := by
    cases hsab : search_arg f P R a b with
    | none => rfl
    | some y => exact absurd hsab (h y)
  rw [search_arg_none] at hnone
  exact hnone x hrange hpx

theorem search_arg_pred (a b x : ℕ) :
    search_arg f P R a b = some x → P (f x) = true := by
  induction b generalizing x with
  | zero =>
    simp only [search_arg]; split_ifs <;> simp
  | succ n IH =>
    simp only [search_arg]
    by_cases h : a < n + 1
    · simp only [if_pos h]
      cases hsa : search_arg f P R a n with
      | none =>
        simp only []
        split_ifs with hp
        · intro hx; have := Option.some.inj hx; subst this; exact hp
        · simp
      | some q =>
        simp only []
        split_ifs with hpq
        · intro hx; have := Option.some.inj hx; subst this
          exact (Bool.and_eq_true_iff.mp hpq).1
        · intro hx; have := Option.some.inj hx; subst this
          exact IH q hsa
    · simp only [if_neg h]; simp

theorem search_arg_in_range (a b x : ℕ) :
    search_arg f P R a b = some x → a ≤ x ∧ x < b := by
  induction b generalizing x with
  | zero =>
    simp only [search_arg]; split_ifs <;> simp
  | succ n IH =>
    simp only [search_arg]
    by_cases h : a < n + 1
    · simp only [if_pos h]
      cases hsa : search_arg f P R a n with
      | none =>
        simp only []
        split_ifs with hp
        · intro hx; have := Option.some.inj hx; subst this
          constructor <;> omega
        · simp
      | some q =>
        simp only []
        split_ifs with hpq
        · intro hx; have := Option.some.inj hx; subst this
          constructor <;> omega
        · intro hx; have := Option.some.inj hx; subst this
          have hiq := IH q hsa
          exact ⟨hiq.1, by omega⟩
    · simp only [if_neg h]; simp

variable (R_reflexive : ∀ x, R x x = true)
variable (R_transitive : ∀ x y z, R x y = true → R y z = true → R x z = true)
variable (R_total : ∀ x y, R x y = true ∨ R y x = true)

include R_reflexive R_transitive R_total in
theorem search_arg_extremum (a b x : ℕ) :
    search_arg f P R a b = some x →
    ∀ y, a ≤ y ∧ y < b → P (f y) = true → R (f x) (f y) = true := by
  induction b generalizing x with
  | zero =>
    simp only [search_arg]
    intro h
    exact absurd h (by split_ifs <;> exact fun h => nomatch h)
  | succ n IH =>
    simp only [search_arg]
    by_cases hab : a < n + 1
    · simp only [if_pos hab]
      cases hsa : search_arg f P R a n with
      | none =>
        simp only []
        by_cases hp : P (f n) = true
        · simp only [if_pos hp]
          intro hx y ⟨hay, hpfy⟩
          have heq := Option.some.inj hx; subst heq
          intro hpfy_val
          by_cases hyn : y < n
          · exfalso
            rw [search_arg_none] at hsa
            exact hsa y ⟨hay, hyn⟩ hpfy_val
          · have hyn_eq : y = n := by omega
            rw [hyn_eq]
            exact R_reflexive (f n)
        · simp only [if_neg hp]
          intro h; exact absurd h (fun h => nomatch h)
      | some q =>
        simp only []
        by_cases hpq : (P (f n) && R (f n) (f q)) = true
        · simp only [if_pos hpq]
          intro hx y ⟨hay, hpfy⟩
          have heq := Option.some.inj hx; subst heq
          intro hpfy_val
          have hpn := (Bool.and_eq_true_iff.mp hpq).1
          have hrq := (Bool.and_eq_true_iff.mp hpq).2
          by_cases hyn : y < n
          · have hiq := IH q hsa y ⟨hay, hyn⟩ hpfy_val
            exact R_transitive _ _ _ hrq hiq
          · have hyn_eq : y = n := by omega
            rw [hyn_eq]
            exact R_reflexive (f n)
        · simp only [if_neg hpq]
          intro hx y ⟨hay, hpfy⟩
          have heq := Option.some.inj hx; subst heq
          intro hpfy_val
          by_cases hyn : y < n
          · exact IH q hsa y ⟨hay, hyn⟩ hpfy_val
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
      intro h; exact absurd h (fun h => nomatch h)


end ArgSearch

section ExMinn

theorem prop_on_ex_minn
    (P : ℕ → Prop) (pred : ℕ → Bool) [DecidablePred (fun n => pred n = true)]
    (ex : ∃ n, pred n = true) :
    P (Nat.find ex) →
    ∃ n, P n ∧ pred n = true ∧ ∀ n', pred n' = true → n ≤ n' := by
  intro hP
  exact ⟨Nat.find ex, hP, Nat.find_spec ex, fun n' hn' => Nat.find_min' ex hn'⟩

theorem ex_minn_le_ex
    (P : ℕ → Bool) [DecidablePred (fun n => P n = true)]
    (exP : ∃ n, P n = true) (c : ℕ) :
    P c = true →
    Nat.find exP ≤ c := by
  intro hPc
  exact Nat.find_min' exP hPc

end ExMinn

end Prosa.Util.Search_arg
