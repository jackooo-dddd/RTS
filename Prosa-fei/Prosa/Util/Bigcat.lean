-- Translated from: ../rt-proofs/util/bigcat.v
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Tactic
import Prosa.Util.Tactics

namespace Prosa.Util.Bigcat

/-- Big concatenation of lists `f m, f (m+1), ..., f (n-1)`. -/
def bigcat_nat {α : Type _} (f : ℕ → List α) (m n : ℕ) : List α :=
  ((List.range' m (n - m)).map f).flatten

section BigCatLemmas

variable {T : Type _} [DecidableEq T]

theorem mem_bigcat_nat (x : T) (m n j : ℕ) (f : ℕ → List T)
    (h_range : m ≤ j ∧ j < n)
    (h_mem : x ∈ f j) :
    x ∈ bigcat_nat f m n := by
  unfold bigcat_nat
  simp only [List.mem_flatten, List.mem_map]
  refine ⟨f j, ⟨j, ?_, rfl⟩, h_mem⟩
  rw [List.mem_range']
  exact ⟨j - m, by omega, by omega⟩

theorem mem_bigcat_nat_exists (x : T) (m n : ℕ) (f : ℕ → List T)
    (h_mem : x ∈ bigcat_nat f m n) :
    ∃ i, x ∈ f i ∧ m ≤ i ∧ i < n := by
  unfold bigcat_nat at h_mem
  simp only [List.mem_flatten, List.mem_map] at h_mem
  obtain ⟨l, ⟨i, h_i_range, rfl⟩, h_x_in⟩ := h_mem
  rw [List.mem_range'] at h_i_range
  obtain ⟨k, hk_lt, rfl⟩ := h_i_range
  exact ⟨m + 1 * k, h_x_in, by omega, by omega⟩

theorem bigcat_nat_uniq (n1 n2 : ℕ) (F : ℕ → List T)
    (h_single : ∀ i, (F i).Nodup)
    (h_uniq : ∀ x i1 i2, x ∈ F i1 → x ∈ F i2 → i1 = i2) :
    (bigcat_nat F n1 n2).Nodup := by
  unfold bigcat_nat
  suffices h : ∀ k s, (List.map F (List.range' s k)).flatten.Nodup from h _ _
  intro k
  induction k with
  | zero => simp
  | succ d ih =>
    intro s
    rw [List.range'_concat]
    simp only [List.map_append, List.flatten_append, List.map_cons,
      List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Nat.one_mul]
    rw [List.nodup_append]
    refine ⟨ih s, h_single (s + d), ?_⟩
    intro a ha b hb hab
    have hb' : a ∈ F (s + d) := hab ▸ hb
    have ⟨i, hi_mem, hi_le, hi_lt⟩ := mem_bigcat_nat_exists a s (s + d) F (by
      unfold bigcat_nat; rwa [show s + d - s = d by omega])
    exact absurd (h_uniq a i (s + d) hi_mem hb') (by omega)

end BigCatLemmas

end Prosa.Util.Bigcat
