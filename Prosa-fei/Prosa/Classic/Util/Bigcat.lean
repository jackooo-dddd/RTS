-- Translated from: ../rt-proofs/classic/util/bigcat.v
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Prosa.Util.Bigcat
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Bigcat

open Prosa.Util.Bigcat

/-- Big concatenation of lists indexed by `Fin n`. -/
def bigcat_ord {α : Type _} (n : ℕ) (f : Fin n → List α) : List α :=
  (List.finRange n |>.map f).flatten

section BigCatLemmas

variable {T : Type _} [DecidableEq T]

theorem mem_bigcat_ord (x : T) (n : ℕ) (j : Fin n) (f : Fin n → List T)
    (h_lt : j.val < n)
    (h_mem : x ∈ f j) :
    x ∈ bigcat_ord n f := by
  unfold bigcat_ord
  simp only [List.mem_flatten, List.mem_map]
  exact ⟨f j, ⟨j, List.mem_finRange j, rfl⟩, h_mem⟩

theorem mem_bigcat_ord_exists (x : T) (n : ℕ) (f : Fin n → List T)
    (h_mem : x ∈ bigcat_ord n f) :
    ∃ i : Fin n, x ∈ f i := by
  unfold bigcat_ord at h_mem
  simp only [List.mem_flatten, List.mem_map] at h_mem
  obtain ⟨l, ⟨i, _, rfl⟩, h_x_in⟩ := h_mem
  exact ⟨i, h_x_in⟩

theorem bigcat_ord_uniq (n : ℕ) (f : Fin n → List T)
    (h_single : ∀ i, (f i).Nodup)
    (h_uniq : ∀ x (i1 i2 : Fin n), x ∈ f i1 → x ∈ f i2 → i1 = i2) :
    (bigcat_ord n f).Nodup := by
  unfold bigcat_ord
  suffices h : ∀ (ls : List (Fin n)), ls.Nodup →
      (ls.map f).flatten.Nodup from h _ (List.nodup_finRange n)
  intro ls hls
  induction ls with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [List.nodup_append]
    have hls_nodup := List.nodup_cons.mp hls
    refine ⟨h_single hd, ih hls_nodup.2, ?_⟩
    intro a ha b hb hab
    subst hab
    rw [List.mem_flatten] at hb
    obtain ⟨l, hl_mem, ha_in⟩ := hb
    rw [List.mem_map] at hl_mem
    obtain ⟨i, hi_mem, rfl⟩ := hl_mem
    have heq := h_uniq a hd i ha ha_in
    subst heq
    exact hls_nodup.1 hi_mem

theorem map_bigcat_ord {T' : Type _} (n : ℕ) (f : Fin n → List T) (g : T → T') :
    List.map g (bigcat_ord n f) = bigcat_ord n (fun i => List.map g (f i)) := by
  unfold bigcat_ord
  rw [List.map_flatten, List.map_map]
  rfl

theorem size_bigcat_ord (n : ℕ) (f : Fin n → List T) :
    (bigcat_ord n f).length = ∑ i : Fin n, (f i).length := by
  unfold bigcat_ord
  rw [List.length_flatten, List.map_map]
  change (List.finRange n |>.map (fun i => (f i).length)).sum = _
  exact Eq.symm (Fin.sum_univ_def (fun i => (f i).length))

theorem size_bigcat_ord_max (n : ℕ) (f : Fin n → List T) (m : ℕ)
    (h_size : ∀ x : Fin n, (f x).length ≤ m) :
    (bigcat_ord n f).length ≤ m * n := by
  rw [size_bigcat_ord]
  calc ∑ i : Fin n, (f i).length
      ≤ ∑ _i : Fin n, m := Finset.sum_le_sum (fun i _ => h_size i)
    _ = m * n := by simp [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

end BigCatLemmas

end Prosa.Classic.Util.Bigcat
