-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/bigcat.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 13)

import Prosa.Util.Bigcat
import Prosa.Classic.Util.Notation
import Prosa.Classic.Util.Bigord
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Subperm

/-!
Lemmas about big concatenation over ordinals.  The source re-exports
`prosa.util.bigcat` (imported above).

Representation notes: `'I_n` is `Fin n`; MathComp's `\cat_(i < n) f i`
(`\big[cat/nil]` over `'I_n` in increasing order) is
`Prosa.Util.Bigcat.bigCatFin f`, the map-then-flatten form also used for the
v0.6 big-concatenation helpers; `\sum_(i < n) F i` over ordinals is Mathlib's
`∑ i : Fin n, F i`.
-/

namespace Prosa.Classic.Util.Bigcat

open BigOperators

universe u v

theorem mem_bigcat_ord :
    ∀ (T : Type u) [DecidableEq T] (x : T) (n : Nat) (j : Fin n) (f : Fin n → List T),
      j.val < n →
      x ∈ f j →
      x ∈ Prosa.Util.Bigcat.bigCatFin f := by
  intro T _ x n j f _ IN
  unfold Prosa.Util.Bigcat.bigCatFin; rw [List.ofFn_eq_map]
  exact List.mem_flatten.mpr ⟨f j, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, IN⟩

theorem mem_bigcat_ord_exists :
    ∀ (T : Type u) [DecidableEq T] (x : T) (n : Nat) (f : Fin n → List T),
      x ∈ Prosa.Util.Bigcat.bigCatFin f →
      ∃ i, x ∈ f i := by
  intro T _ x n f IN
  unfold Prosa.Util.Bigcat.bigCatFin at IN; rw [List.ofFn_eq_map] at IN
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp IN
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  exact ⟨i, hx⟩

theorem bigcat_ord_uniq :
    ∀ (T : Type u) [DecidableEq T] (n : Nat) (f : Fin n → List T),
      (∀ i, (f i).Nodup) →
      (∀ x i1 i2, x ∈ f i1 → x ∈ f i2 → i1 = i2) →
      (Prosa.Util.Bigcat.bigCatFin f).Nodup := by
  intro T _ n f SINGLE UNIQ
  unfold Prosa.Util.Bigcat.bigCatFin; rw [List.ofFn_eq_map, List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact SINGLE i
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (R := fun a b => a ≠ b) ?_ (List.nodup_finRange n)
    intro a b _ _ hab
    rw [List.disjoint_left]
    intro x ha hb
    exact hab (UNIQ x a b ha hb)

theorem map_bigcat_ord {T : Type u} {T' : Type v} (n : Nat) (f : Fin n → List T)
    (g : T → T') :
    (Prosa.Util.Bigcat.bigCatFin f).map g =
      Prosa.Util.Bigcat.bigCatFin (fun i => (f i).map g) := by
  simp [Prosa.Util.Bigcat.bigCatFin, List.ofFn_eq_map, List.map_flatten, Function.comp_def]

theorem size_bigcat_ord {T : Type u} (n : Nat) (f : Fin n → List T) :
    (Prosa.Util.Bigcat.bigCatFin f).length = ∑ i : Fin n, (f i).length := by
  unfold Prosa.Util.Bigcat.bigCatFin
  rw [List.ofFn_eq_map, List.length_flatten, Fin.sum_univ_def, List.map_map]
  rfl

theorem size_bigcat_ord_max {T : Type u} (n : Nat) (f : Fin n → List T) (m : Nat) :
    (∀ x, (f x).length ≤ m) →
    (Prosa.Util.Bigcat.bigCatFin f).length ≤ m * n := by
  intro SIZE
  rw [size_bigcat_ord]
  calc ∑ i : Fin n, (f i).length ≤ ∑ _i : Fin n, m := Finset.sum_le_sum fun i _ => SIZE i
    _ = m * n := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

end Prosa.Classic.Util.Bigcat
