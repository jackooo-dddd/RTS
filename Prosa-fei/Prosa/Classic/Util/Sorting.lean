-- Translated from: ../rt-proofs/classic/util/sorting.v
import Mathlib
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Sorting

open List

section Sorting

  section SortedImplLeIdx

    variable {T : Type _} [DecidableEq T]
    variable (leT : T → T → Bool)
    variable (xs : List T)
    variable (default : T)

    lemma sort_ordered (idx : ℕ)
        (SORT : List.IsChain (fun a b => leT a b = true) xs)
        (LT : idx < xs.length - 1) :
        leT (xs.getD idx default) (xs.getD (idx + 1) default) = true := by
      rw [List.isChain_iff_getElem] at SORT
      have hlen : idx + 1 < xs.length := by omega
      rw [List.getD_eq_getElem xs default (by omega), List.getD_eq_getElem xs default hlen]
      exact SORT idx hlen

    lemma sorted_rcons_prefix (x : T)
        (SORT : List.IsChain (fun a b => leT a b = true) (xs ++ [x])) :
        List.IsChain (fun a b => leT a b = true) xs := by
      rw [List.isChain_append] at SORT
      exact SORT.1

    lemma order_sorted_rcons (x lst : T)
        (H_leT_is_transitive : ∀ (y x z : T),
          leT x y = true → leT y z = true → leT x z = true)
        (SORT : List.IsChain (fun a b => leT a b = true) (xs ++ [lst]))
        (IN : x ∈ xs) :
        leT x lst = true := by
      revert x IN
      induction xs with
      | nil => intro x hx; simp at hx
      | cons a tl ih =>
        intro y hy_in
        rw [List.cons_append] at SORT
        rw [List.isChain_cons] at SORT
        obtain ⟨hhead, SORT_tl⟩ := SORT
        rcases List.mem_cons.mp hy_in with rfl | hin
        · -- y = a
          cases htl : tl with
          | nil =>
            rw [htl] at hhead
            simp [List.head?] at hhead
            exact hhead
          | cons b rest =>
            rw [htl] at hhead SORT_tl ih
            simp [List.head?] at hhead
            have hb_lst : leT b lst = true := ih SORT_tl b (by simp)
            exact H_leT_is_transitive _ _ _ hhead hb_lst
        · exact ih SORT_tl y hin

    lemma sorted_lt_idx_implies_rel (i1 i2 : ℕ)
        (H_leT_is_transitive : ∀ (y x z : T),
          leT x y = true → leT y z = true → leT x z = true)
        (SORT : List.IsChain (fun a b => leT a b = true) xs)
        (LE : i1 < i2)
        (LEsize : i2 < xs.length) :
        leT (xs.getD i1 default) (xs.getD i2 default) = true := by
      have ⟨delta, hdelta⟩ : ∃ d, i2 = i1 + 1 + d := ⟨i2 - i1 - 1, by omega⟩
      subst hdelta
      clear LE
      induction delta with
      | zero =>
        simp only [Nat.add_zero]
        exact sort_ordered leT xs default i1 SORT (by omega)
      | succ d ih =>
        have ih' := ih (by omega)
        have step := sort_ordered leT xs default (i1 + 1 + d) SORT (by omega)
        exact H_leT_is_transitive _ _ _ ih' step

    lemma sorted_rel_implies_le_idx (i1 i2 : ℕ)
        (H_leT_is_transitive : ∀ (y x z : T),
          leT x y = true → leT y z = true → leT x z = true)
        (UNIQ : xs.Nodup)
        (ANTI : ∀ x1 x2, x1 ∈ xs → x2 ∈ xs →
          leT x1 x2 = true → leT x2 x1 = true → x1 = x2)
        (SORT : List.IsChain (fun a b => leT a b = true) xs)
        (REL : leT (xs.getD i1 default) (xs.getD i2 default) = true)
        (SIZE1 : i1 < xs.length)
        (SIZE2 : i2 < xs.length) :
        i1 ≤ i2 := by
      by_contra h
      push_neg at h
      have REL' := sorted_lt_idx_implies_rel leT xs default i2 i1 H_leT_is_transitive SORT h SIZE1
      have hmem1 : xs.getD i1 default ∈ xs := by
        rw [List.getD_eq_getElem _ _ SIZE1]; exact List.getElem_mem SIZE1
      have hmem2 : xs.getD i2 default ∈ xs := by
        rw [List.getD_eq_getElem _ _ SIZE2]; exact List.getElem_mem SIZE2
      have EQ := ANTI _ _ hmem1 hmem2 REL REL'
      rw [List.getD_eq_getElem _ _ SIZE1, List.getD_eq_getElem _ _ SIZE2] at EQ
      have hne : i1 ≠ i2 := by omega
      rw [List.nodup_iff_getElem?_ne_getElem?] at UNIQ
      exact absurd (by simp [SIZE2, SIZE1, EQ]) (UNIQ i2 i1 h SIZE1)

  end SortedImplLeIdx

  lemma prev_le_next {T : Type _} (F : T → ℕ) (xs : List T) (d : T) (i k : ℕ)
      (ALL : ∀ i, i < xs.length - 1 → F (xs.getD i d) ≤ F (xs.getD (i + 1) d))
      (SIZE : i + k ≤ xs.length - 1) :
      F (xs.getD i d) ≤ F (xs.getD (i + k) d) := by
      induction k with
      | zero => simp
      | succ n ih =>
        have h1 : i + n ≤ xs.length - 1 := by omega
        have h2 : i + n < xs.length - 1 := by omega
        calc F (xs.getD i d) ≤ F (xs.getD (i + n) d) := ih h1
          _ ≤ F (xs.getD (i + n + 1) d) := ALL (i + n) h2
          _ = F (xs.getD (i + (n + 1)) d) := by ring_nf

end Sorting

end Prosa.Classic.Util.Sorting
