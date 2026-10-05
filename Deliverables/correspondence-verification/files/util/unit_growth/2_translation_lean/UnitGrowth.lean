-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/unit_growth.v

import Mathlib.Tactic
import Prosa.Util.Rel

namespace Prosa.Util.UnitGrowth

/-- A function grows by at most one at every successor step. -/
def unit_growth_function (f : Nat → Nat) : Prop :=
  ∀ t, f (t + 1) ≤ f t + 1

theorem unit_growth_function_k_steps_bounded
    (f : Nat → Nat) (hunit : unit_growth_function f) :
    ∀ x k, f (x + k) ≤ k + f x := by
  intro x k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        f (x + (k + 1)) ≤ f (x + k) + 1 := by
          simpa [Nat.add_assoc] using hunit (x + k)
        _ ≤ (k + 1) + f x := by omega

theorem exists_intermediate_point
    (f : Nat → Nat) (hunit : unit_growth_function f)
    (x1 x2 : Nat) (hinterval : x1 ≤ x2)
    (y : Nat) (hbetween : f x1 ≤ y ∧ y < f x2) :
    ∃ xmid, (x1 ≤ xmid ∧ xmid < x2) ∧ f xmid = y := by
  suffices h : ∀ delta,
      f x1 ≤ y ∧ y < f (x1 + delta) →
        ∃ xmid, (x1 ≤ xmid ∧ xmid < x1 + delta) ∧ f xmid = y by
    obtain ⟨xmid, hxmid, hfx⟩ := h (x2 - x1) ⟨hbetween.1, by
      simpa [Nat.add_sub_of_le hinterval] using hbetween.2⟩
    exact ⟨xmid, ⟨hxmid.1, by omega⟩, hfx⟩
  intro delta
  induction delta with
  | zero =>
      simp only [Nat.add_zero]
      intro h
      omega
  | succ n ih =>
      intro h
      have hstep := hunit (x1 + n)
      have hstep' : f (x1 + (n + 1)) ≤ f (x1 + n) + 1 := by
        simpa [Nat.add_assoc] using hstep
      by_cases hle : y ≤ f (x1 + n)
      · by_cases heq : f (x1 + n) = y
        · exact ⟨x1 + n, ⟨Nat.le_add_right x1 n, by omega⟩, heq⟩
        · obtain ⟨xmid, hxmid, hfx⟩ := ih ⟨h.1, by omega⟩
          exact ⟨xmid, ⟨hxmid.1, by omega⟩, hfx⟩
      · omega

theorem exists_intermediate_point_leq
    (f : Nat → Nat) (hunit : unit_growth_function f)
    (x1 x2 : Nat) (hinterval : x1 ≤ x2)
    (y : Nat) (hbetween : f x1 ≤ y ∧ y ≤ f x2) :
    ∃ xmid, (x1 ≤ xmid ∧ xmid ≤ x2) ∧ f xmid = y := by
  rcases eq_or_lt_of_le hbetween.2 with heq | hlt
  · exact ⟨x2, ⟨hinterval, Nat.le_refl _⟩, heq.symm⟩
  · obtain ⟨xmid, hxmid, hfx⟩ :=
      exists_intermediate_point f hunit x1 x2 hinterval y ⟨hbetween.1, hlt⟩
    exact ⟨xmid, ⟨hxmid.1, Nat.le_of_lt hxmid.2⟩, hfx⟩

theorem exists_first_intermediate_point
    (P : Nat → Bool) (t1 t2 : Nat)
    (ht12 : t1 ≤ t2) (hnot : P t1 = false) (hat : P t2 = true) :
    ∃ t, (t1 < t ∧ t ≤ t2) ∧
      (∀ x, t1 ≤ x ∧ x < t → P x = false) ∧ P t = true := by
  have htlt : t1 < t2 := by
    rcases Nat.eq_or_lt_of_le ht12 with heq | hlt
    · subst t2
      simp_all
    · exact hlt
  have hex : ∃ n, P (t1 + 1 + n) = true ∧ t1 + 1 + n ≤ t2 := by
    refine ⟨t2 - (t1 + 1), ?_⟩
    have heq : t1 + 1 + (t2 - (t1 + 1)) = t2 := by omega
    exact ⟨by simpa [heq] using hat, by omega⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  refine ⟨t1 + 1 + m, ⟨by omega, hm.2⟩, ?_, hm.1⟩
  intro x hx
  by_cases hxge : t1 + 1 ≤ x
  · have hxm : x - (t1 + 1) < m := by omega
    have hmin := Nat.find_min hex hxm
    cases hpx : P x with
    | false => rfl
    | true =>
        exfalso
        apply hmin
        have heq : t1 + 1 + (x - (t1 + 1)) = x := by omega
        exact ⟨by simpa [heq] using hpx, by omega⟩
  · have hxeq : x = t1 := by omega
    simpa [hxeq] using hnot

/-- Slow a natural-valued function so that each successor step grows by at
most one. -/
def slowed (F : Nat → Nat) : Nat → Nat
  | 0 => F 0
  | n + 1 => min (F (n + 1)) (slowed F n + 1)

theorem slowed_respects_pointwise_leq
    (f F : Nat → Nat) (Δ : Nat)
    (hunit : unit_growth_function f)
    (hle : ∀ x, x ≤ Δ → f x ≤ F x) :
    f Δ ≤ slowed F Δ := by
  induction Δ with
  | zero => simpa [slowed] using hle 0 (Nat.le_refl 0)
  | succ n ih =>
      rw [slowed]
      apply Nat.le_min.mpr
      constructor
      · exact hle (n + 1) (Nat.le_refl _)
      · calc
          f (n + 1) ≤ f n + 1 := by simpa using hunit n
          _ ≤ slowed F n + 1 := Nat.add_le_add_right
            (ih (fun x hx => hle x (Nat.le_trans hx (Nat.le_succ n)))) 1

theorem slowed_is_unit_step (f : Nat → Nat) :
    unit_growth_function (slowed f) := by
  intro n
  simpa [slowed] using Nat.min_le_right (f (n + 1)) (slowed f n + 1)

theorem slowed_respects_monotone
    (f : Nat → Nat)
    (hmono : Prosa.Util.Rel.monotone
      (fun x y : Nat => decide (x ≤ y)) f) :
    Prosa.Util.Rel.monotone
      (fun x y : Nat => decide (x ≤ y)) (slowed f) := by
  have hfmono : ∀ x y, x ≤ y → f x ≤ f y := by
    intro x y hxy
    have h := hmono x y (by simpa using hxy)
    simpa using h
  have hbelow : ∀ n, slowed f n ≤ f n := by
    intro n
    cases n with
    | zero => simp [slowed]
    | succ n => simpa [slowed] using Nat.min_le_left (f (n + 1)) (slowed f n + 1)
  have hstep : ∀ n, slowed f n ≤ slowed f (n + 1) := by
    intro n
    rw [slowed]
    apply Nat.le_min.mpr
    exact ⟨Nat.le_trans (hbelow n) (hfmono n (n + 1) (by omega)), by omega⟩
  intro x y hxyb
  have hxy : x ≤ y := by simpa using hxyb
  have hslow : slowed f x ≤ slowed f y := by
    obtain ⟨d, hy⟩ := Nat.exists_eq_add_of_le hxy
    subst y
    clear hxyb hxy
    induction d with
    | zero => simp
    | succ d ih =>
        exact Nat.le_trans ih (by simpa [Nat.add_assoc] using hstep (x + d))
  simpa using hslow

theorem slowed_never_exceeds (f : Nat → Nat) (x : Nat) :
    slowed f x ≤ f x := by
  cases x with
  | zero => simp [slowed]
  | succ n => simpa [slowed] using Nat.min_le_left (f (n + 1)) (slowed f n + 1)

theorem bound_preserved_under_slowed
    (f : Nat → Nat) (δ A F : Nat)
    (hle : A ≤ F - f δ) :
    A ≤ F - slowed f δ := by
  have hslow := slowed_never_exceeds f δ
  omega

theorem slowed_subtraction_value_preservation
    (f : Nat → Nat) (Δ : Nat)
    (hmono : Prosa.Util.Rel.monotone
      (fun x y : Nat => decide (x ≤ y)) f) :
    ∃ δ, δ ≤ Δ ∧ Δ - f Δ = δ - slowed f δ := by
  let g : Nat → Nat := fun n => n - slowed f n
  have hslowmono : ∀ x y, x ≤ y → slowed f x ≤ slowed f y := by
    intro x y hxy
    have h := slowed_respects_monotone f hmono x y (by simpa using hxy)
    simpa using h
  have hgunit : unit_growth_function g := by
    intro n
    have hs := hslowmono n (n + 1) (by omega)
    dsimp [g]
    omega
  have hbound : g 0 ≤ Δ - f Δ ∧ Δ - f Δ ≤ g Δ := by
    have hs := slowed_never_exceeds f Δ
    constructor
    · simp [g]
    · dsimp [g]
      omega
  obtain ⟨δ, hδ, heq⟩ :=
    exists_intermediate_point_leq g hgunit 0 Δ (Nat.zero_le _) (Δ - f Δ) hbound
  exact ⟨δ, hδ.2, heq.symm⟩

end Prosa.Util.UnitGrowth
