-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/superadditivity.v

import Mathlib.Tactic
import Prosa.Util.List
import Prosa.Util.Nat
import Prosa.Util.Rel

namespace Prosa.Util.Superadditivity

def superadditive_at (f : Nat → Nat) (h : Nat) : Prop :=
  ∀ a b, a + b = h → f a + f b ≤ f h

def superadditive_until (f : Nat → Nat) (h : Nat) : Prop :=
  ∀ x, x < h → superadditive_at f x

def superadditive (f : Nat → Nat) : Prop :=
  ∀ h, superadditive_at f h

def superadditive_standard (f : Nat → Nat) : Prop :=
  ∀ a b, f a + f b ≤ f (a + b)

theorem superadditive_standard_equivalence (f : Nat → Nat) :
    superadditive f ↔ superadditive_standard f := by
  constructor
  · intro hs a b
    exact hs (a + b) a b rfl
  · intro hs h a b hab
    simpa [hab] using hs a b

theorem superadditive_first_zero (f : Nat → Nat)
    (hs : superadditive_at f 0) : f 0 = 0 := by
  have h := hs 0 0 rfl
  omega

theorem superadditive_monotone (f : Nat → Nat)
    (hs : superadditive f) :
    Rel.monotone (fun a b : Nat => decide (a ≤ b)) f := by
  intro x y hxy
  have hxy' : x ≤ y := by simpa using hxy
  have hsum : x + (y - x) = y := by omega
  have hsuper := hs y x (y - x) hsum
  have hle : f x ≤ f x + f (y - x) := Nat.le_add_right _ _
  apply decide_eq_true
  omega

theorem superadditive_leq_mul (f : Nat → Nat)
    (hs : superadditive f) (n m : Nat) :
    m * f n ≤ f (m * n) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsuper := hs ((m + 1) * n) (m * n) n (by simp [Nat.succ_mul])
      simpa [Nat.succ_mul, Nat.add_mul] using
        Nat.le_trans (Nat.add_le_add_right ih (f n)) hsuper

theorem superadditive_unbounded (f : Nat → Nat)
    (hs : superadditive f)
    (hpos : ∃ n, 0 < f n) (t : Nat) :
    ∃ n', t ≤ f n' := by
  obtain ⟨n, hn⟩ := hpos
  refine ⟨t * n, ?_⟩
  have hmul := superadditive_leq_mul f hs n t
  have hunit : t * 1 ≤ t * f n :=
    Nat.mul_le_mul_left t (Nat.succ_le_iff.mpr hn)
  simpa using Nat.le_trans hunit hmul

/-- The source's ordered `index_iota 1 h` sequence is mapped, not converted
to a set: its order and multiplicity remain observable in the computation. -/
def minimal_superadditive_extension (f : Nat → Nat) (h : Nat) : Nat :=
  List.max0 ((List.index_iota 1 h).map (fun a => f a + f (h - a)))

theorem minimal_extension_superadditive_at_horizon
    (f : Nat → Nat) (h : Nat)
    (hs : superadditive_until f h)
    (f' : Nat → Nat)
    (hfp : ∀ t, f' t =
      if decide (t = h) then minimal_superadditive_extension f h else f t) :
    superadditive_at f' h := by
  intro a b hab
  by_cases hh : h = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a; subst b; subst h
    simp [hfp, minimal_superadditive_extension, List.index_iota, List.max0]
  by_cases ha : a = 0
  · subst a
    have hzero : f 0 = 0 :=
      superadditive_first_zero f (hs 0 (by omega))
    have hb : b = h := by omega
    subst b
    rw [hfp 0, hfp h]
    simp [Ne.symm hh, hzero]
  by_cases hb : b = 0
  · subst b
    have hzero : f 0 = 0 :=
      superadditive_first_zero f (hs 0 (by omega))
    have ha' : a = h := by omega
    subst a
    rw [hfp 0, hfp h]
    simp [Ne.symm hh, hzero]
  have ha_lt : a < h := by omega
  have hb_lt : b < h := by omega
  have ha_ne : a ≠ h := by omega
  have hb_ne : b ≠ h := by omega
  have hin : a ∈ List.index_iota 1 h := by
    simp only [List.index_iota, List.mem_range']
    refine ⟨a - 1, by omega, ?_⟩
    omega
  have hmap : f a + f (h - a) ∈
      (List.index_iota 1 h).map (fun x => f x + f (h - x)) :=
    List.mem_map.mpr ⟨a, hin, rfl⟩
  have hbound := List.in_max0_le _ _ hmap
  have hsub : h - a = b := by omega
  rw [hfp a, hfp b, hfp h]
  simpa [ha_ne, hb_ne, hsub, minimal_superadditive_extension] using hbound

theorem minimal_extension_superadditive_until
    (f : Nat → Nat) (h : Nat)
    (hs : superadditive_until f h)
    (f' : Nat → Nat)
    (hfp : ∀ t, f' t =
      if decide (t = h) then minimal_superadditive_extension f h else f t) :
    superadditive_until f' (h + 1) := by
  intro t ht
  by_cases heq : t = h
  · subst t
    exact minimal_extension_superadditive_at_horizon f h hs f' hfp
  · have hlt : t < h := by omega
    intro a b hab
    have ha : a < h := by omega
    have hb : b < h := by omega
    simpa [hfp, heq, ne_of_lt ha, ne_of_lt hb] using
      (hs t hlt a b hab)

end Prosa.Util.Superadditivity
