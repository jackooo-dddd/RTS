-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/nondecreasing.v
import Mathlib
import Prosa.Util.Epsilon
import Prosa.Util.Nat
import Prosa.Util.List

namespace Prosa.Util.Nondecreasing

open Prosa.Util.List
open Prosa.Util.Epsilon

/-- LEAN_HELPER: direct spelling of MathComp's zero-defaulted `nth`. -/
private abbrev nthD (xs : List Nat) (n : Nat) : Nat := xs.getD n 0

section NondecreasingSequence

section Definitions

  def nondecreasing_sequence (xs : List ℕ) : Prop :=
    ∀ n1 n2, n1 ≤ n2 ∧ n2 < xs.length → nthD xs n1 ≤ nthD xs n2

  def increasing_sequence (xs : List ℕ) : Prop :=
    ∀ n1 n2, n1 < n2 ∧ n2 < xs.length → nthD xs n1 < nthD xs n2

  def distances (xs : List ℕ) : List ℕ :=
    (xs.zip (xs.drop 1)).map (fun p => p.2 - p.1)

end Definitions

section IncreasingSequence

  theorem iota_is_increasing_sequence (a b : ℕ) (P : ℕ → Bool) :
      increasing_sequence ((index_iota a b).filter (fun x => P x)) := by
    intro n1 n2 ⟨hlt_n, hlt_len⟩
    set xs := (index_iota a b).filter (fun x => P x) with hxs_def
    simp only [nthD, List.getD]
    have hn2 : n2 < xs.length := hlt_len
    have hn1 : n1 < xs.length := by omega
    rw [List.getElem?_eq_getElem hn1, List.getElem?_eq_getElem hn2]
    simp only [Option.getD]
    have hsorted : xs.Pairwise (· < ·) := by
      rw [hxs_def]
      exact List.Pairwise.filter _ (by
        simp only [index_iota]
        exact List.pairwise_lt_range')
    exact List.pairwise_iff_getElem.mp hsorted n1 n2 hn1 hn2 hlt_n

  theorem increasing_implies_nondecreasing (xs : List ℕ)
      (h : increasing_sequence xs) :
      nondecreasing_sequence xs := by
    intro n1 n2 ⟨hle, hlt⟩
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt1
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (h n1 n2 ⟨hlt1, hlt⟩)

end IncreasingSequence

section NonDecreasingSequence

  theorem nondec_seq_zero_first (xs : List ℕ)
      (h1 : 0 ∈ xs) (h2 : nondecreasing_sequence xs) :
      first0 xs = 0 := by
    match xs with
    | [] => simp at h1
    | 0 :: _ => simp [first0, List.headD]
    | (x + 1) :: xs' =>
      exfalso
      rw [List.mem_cons] at h1
      rcases h1 with h1 | h1
      · omega
      · have ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp h1
        have h0idx := h2 0 (idx + 1) ⟨Nat.zero_le _, by simp; omega⟩
        simp only [nthD, List.getD] at h0idx
        have he0 : (((x + 1) :: xs')[0]?).getD 0 = x + 1 := by simp
        have he1 : (((x + 1) :: xs')[(idx + 1)]?).getD 0 = xs'[idx] := by
          simp [List.getElem?_cons_succ, List.getElem?_eq_getElem hidx]
        rw [he0, he1] at h0idx
        omega

  theorem nondecreasing_sequence_2cons_leVeq (x1 x2 : ℕ) (xs : List ℕ)
      (h : nondecreasing_sequence (x1 :: x2 :: xs)) :
      x1 = x2 ∨ x1 < x2 := by
    have h01 := h 0 1 ⟨Nat.zero_le 1, by simp [List.length]⟩
    simp [nthD, List.getD] at h01
    rcases Nat.eq_or_lt_of_le h01 with heq | hlt
    · left; exact heq
    · right; exact hlt

  theorem nondecreasing_sequence_cons (x : ℕ) (xs : List ℕ)
      (h : nondecreasing_sequence (x :: xs)) :
      nondecreasing_sequence xs := by
    intro n1 n2 ⟨hle, hlt⟩
    have := h (n1 + 1) (n2 + 1) ⟨by omega, by simp [List.length]; omega⟩
    simp [nthD, List.getD, List.getD_cons_succ] at this ⊢
    exact this

  theorem nondecreasing_sequence_add_min (x : ℕ) (xs : List ℕ)
      (h1 : ∀ y, y ∈ xs → x ≤ y)
      (h2 : nondecreasing_sequence xs) :
      nondecreasing_sequence (x :: xs) := by
    intro n1 n2 ⟨hle, hlt⟩
    match n1 with
    | 0 =>
      match n2 with
      | 0 => exact Nat.le_refl _
      | n2 + 1 =>
        simp only [nthD, List.getD, List.length] at *
        have hlen : 0 < xs.length := by omega
        have h_nd := h2 0 n2 ⟨Nat.zero_le _, by omega⟩
        simp only [nthD, List.getD] at h_nd
        apply Nat.le_trans _ h_nd
        apply h1
        have : xs ≠ [] := List.ne_nil_of_length_pos hlen
        match xs, this with
        | a :: _, _ => simp [List.getD]
    | n1 + 1 =>
      match n2 with
      | 0 => omega
      | n2 + 1 =>
        simp only [nthD, List.getD, List.length] at *
        exact h2 n1 n2 ⟨by omega, by omega⟩

  theorem nondecreasing_sequence_cons_double (x : ℕ) (xs : List ℕ)
      (h : nondecreasing_sequence (x :: xs)) :
      nondecreasing_sequence (x :: x :: xs) := by
    intro n1 n2 ⟨hle, hlt⟩
    simp only [List.length] at hlt
    match n1, n2 with
    | 0, 0 => exact Nat.le_refl _
    | 0, 1 => simp [nthD, List.getD]
    | 0, n2 + 2 =>
      simp only [nthD, List.getD] at *
      have := h 0 (n2 + 1) ⟨Nat.zero_le _, by simp [List.length]; omega⟩
      simp only [nthD, List.getD] at this
      exact this
    | 1, 1 => exact Nat.le_refl _
    | 1, n2 + 2 =>
      simp only [nthD, List.getD] at *
      have := h 0 (n2 + 1) ⟨Nat.zero_le _, by simp [List.length]; omega⟩
      simp only [nthD, List.getD] at this
      exact this
    | n1 + 2, n2 + 2 =>
      simp only [nthD, List.getD] at *
      have := h (n1 + 1) (n2 + 1) ⟨by omega, by simp [List.length]; omega⟩
      simp only [nthD, List.getD] at this
      exact this

  theorem nondecreasing_sequence_cons_min (x : ℕ) (xs : List ℕ)
      (h : nondecreasing_sequence (x :: xs)) :
      ∀ y, y ∈ xs → x ≤ y := by
    intro y hy
    have ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hy
    have h0idx := h 0 (idx + 1) ⟨Nat.zero_le _, by simp; omega⟩
    simp only [nthD, List.getD] at h0idx
    have he0 : ((x :: xs)[0]?).getD 0 = x := by simp
    have he1 : ((x :: xs)[(idx + 1)]?).getD 0 = xs[idx] := by
      simp [List.getElem?_cons_succ, List.getElem?_eq_getElem hidx]
    rw [he0, he1] at h0idx
    rw [← hget]; exact h0idx

  theorem nondecreasing_sequence_cons_smin (x1 x2 : ℕ) (xs : List ℕ)
      (h1 : x1 < x2) (h2 : nondecreasing_sequence (x1 :: x2 :: xs)) :
      ∀ y, y ∈ x2 :: xs → x1 < y := by
    intro y hy
    have hnd_tail := nondecreasing_sequence_cons _ _ h2
    have hnd_double := nondecreasing_sequence_cons_double _ _ hnd_tail
    have hmin := nondecreasing_sequence_cons_min _ _ hnd_double y hy
    omega

  theorem antidensity_of_nondecreasing_seq (xs : List ℕ) (x n : ℕ)
      (h1 : nondecreasing_sequence xs)
      (h2 : nthD xs n < x ∧ x < nthD xs (n + 1)) :
      x ∉ xs := by
    intro hmem
    obtain ⟨ind, hind_lt, hind_eq⟩ := List.mem_iff_getElem.mp hmem
    -- x = xs[ind]
    have hx_eq : x = nthD xs ind := by
      simp only [nthD, List.getD, List.getElem?_eq_getElem hind_lt, Option.getD]
      exact hind_eq.symm
    -- If n+1 ≥ xs.length, then xs[n+1] = 0 and x < 0 is impossible
    by_cases hn1 : n + 1 < xs.length
    · -- n < xs.length
      have hn : n < xs.length := by omega
      -- ind > n: otherwise xs[ind] ≤ xs[n] < x = xs[ind], contradiction
      have hgt : n < ind := by
        by_contra hle
        push_neg at hle
        have := h1 ind n ⟨hle, hn⟩
        omega
      -- ind < n+1: otherwise xs[n+1] ≤ xs[ind] and x < xs[n+1] ≤ xs[ind] = x, contradiction
      have hlt : ind < n + 1 := by
        by_contra hge
        push_neg at hge
        have := h1 (n + 1) ind ⟨hge, hind_lt⟩
        omega
      omega
    · push_neg at hn1
      have : nthD xs (n + 1) = 0 := by
        simp only [nthD, List.getD]
        rw [List.getElem?_eq_none (by omega)]; rfl
      omega

  theorem belonging_to_segment_of_seq_is_total (xs : List ℕ) (x : ℕ)
      (h1 : 2 ≤ xs.length)
      (h2 : first0 xs ≤ x ∧ x < last0 xs) :
      ∃ n, n + 1 < xs.length ∧ nthD xs n ≤ x ∧ x < nthD xs (n + 1) := by
    induction xs with
    | nil => simp at h1
    | cons a tl ih =>
      cases tl with
      | nil => simp at h1
      | cons b rest =>
        by_cases hlt : x < b
        · refine ⟨0, by simp, ?_, ?_⟩
          · simp [first0, List.headD] at h2; simp [nthD, List.getD]; exact h2.1
          · simp [nthD, List.getD]; exact hlt
        · push_neg at hlt
          cases rest with
          | nil =>
            refine ⟨0, by simp, ?_, ?_⟩
            · simp [first0, List.headD] at h2; simp [nthD, List.getD]; exact h2.1
            · simp [nthD, List.getD, last0, List.getLastD] at h2 ⊢; exact h2.2
          | cons c rest' =>
            have h1' : 2 ≤ (b :: c :: rest').length := by simp
            have h2' : first0 (b :: c :: rest') ≤ x ∧ x < last0 (b :: c :: rest') := by
              constructor
              · simp [first0, List.headD]; exact hlt
              · rw [last0_cons a (b :: c :: rest') (by simp)] at h2; exact h2.2
            obtain ⟨n, hn1, hn2, hn3⟩ := ih h1' h2'
            have hlen : n + 1 + 1 < (a :: b :: c :: rest').length := by
              simp only [List.length_cons] at hn1 ⊢; omega
            refine ⟨n + 1, hlen, ?_, ?_⟩
            · show nthD (a :: b :: c :: rest') (n + 1) ≤ x
              have : nthD (a :: b :: c :: rest') (n + 1) = nthD (b :: c :: rest') n := by
                simp only [nthD, List.getD, List.getElem?_cons_succ]
              rw [this]; exact hn2
            · show x < nthD (a :: b :: c :: rest') (n + 1 + 1)
              have : nthD (a :: b :: c :: rest') (n + 1 + 1) = nthD (b :: c :: rest') (n + 1) := by
                simp only [nthD, List.getD]
                show ((a :: b :: c :: rest')[(n + 2)]?).getD 0 = ((b :: c :: rest')[(n + 1)]?).getD 0
                simp [List.getElem?_cons_succ]
              rw [this]; exact hn3

  theorem last_is_max_in_nondecreasing_seq (xs : List ℕ) (x : ℕ)
      (h1 : nondecreasing_sequence xs) (h2 : x ∈ xs) :
      x ≤ last0 xs := by
    rw [List.mem_iff_getElem] at h2
    obtain ⟨idx, hidx, hget⟩ := h2
    rw [last0_nth]
    have hxeq : x = nthD xs idx := by
      simp only [nthD, List.getD, List.getElem?_eq_getElem hidx, Option.getD]
      exact hget.symm
    rw [hxeq]
    have hle : idx ≤ xs.length - 1 := by omega
    exact h1 idx (xs.length - 1) ⟨hle, by omega⟩

end NonDecreasingSequence

section Undup

  theorem nodup_sort_2cons_eq {X : Type _} [DecidableEq X] (x : X) (xs : List X) :
      (x :: x :: xs).dedup = (x :: xs).dedup := by
    simp [List.dedup_cons, List.mem_dedup, List.mem_cons]

  theorem nodup_sort_2cons_lt (x1 x2 : ℕ) (xs : List ℕ)
      (h1 : x1 < x2) (h2 : nondecreasing_sequence (x1 :: x2 :: xs)) :
      (x1 :: x2 :: xs).dedup = x1 :: (x2 :: xs).dedup := by
    simp only [List.dedup_cons]
    have hne : x1 ≠ x2 := by omega
    have hnd_tail := nondecreasing_sequence_cons _ _ h2
    have hmin := nondecreasing_sequence_cons_min _ _ hnd_tail
    have hnotin : x1 ∉ xs := by
      intro hmem
      have := hmin x1 hmem
      omega
    have hnotin2 : x1 ∉ x2 :: xs := by
      simp [List.mem_cons, hne, hnotin]
    simp [List.mem_dedup, hnotin2]

  theorem last0_undup (xs : List ℕ)
      (h : nondecreasing_sequence xs) :
      last0 xs.dedup = last0 xs := by
    induction xs with
    | nil => rfl
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        simp only [List.dedup_cons, List.not_mem_nil, ↓reduceIte,
          List.dedup_nil]
      | cons x2 rest =>
        rcases nondecreasing_sequence_2cons_leVeq x1 x2 rest h with heq | hlt
        · subst heq  -- x1 is now x2, so the sequence is x2 :: x2 :: rest
          rw [nodup_sort_2cons_eq]
          rw [ih (nondecreasing_sequence_cons _ _ h)]
          rw [last0_cons _ _ (by simp : (_ :: rest) ≠ [])]
        · rw [nodup_sort_2cons_lt x1 x2 rest hlt h]
          have hdedup_ne : (x2 :: rest).dedup ≠ [] := by
            intro heq'
            have hmem := List.mem_dedup.mpr (show x2 ∈ x2 :: rest from List.mem_cons_self)
            rw [heq'] at hmem; exact (List.not_mem_nil hmem).elim
          rw [last0_cons x1 _ hdedup_ne]
          rw [ih (nondecreasing_sequence_cons _ _ h)]
          rw [last0_cons x1 (x2 :: rest) (by simp)]

  theorem nondecreasing_sequence_undup (xs : List ℕ)
      (h : nondecreasing_sequence xs) :
      nondecreasing_sequence xs.dedup := by
    induction xs with
    | nil => intro n1 n2 ⟨_, hlt⟩; simp at hlt
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        simp only [List.dedup_cons, List.not_mem_nil, ↓reduceIte, List.dedup_nil]
        intro n1 n2 ⟨hle, hlt⟩
        simp [List.length] at hlt
        have hn2 : n2 = 0 := by omega
        have hn1 : n1 = 0 := by omega
        subst hn2; subst hn1; exact le_refl _
      | cons x2 rest =>
        rcases nondecreasing_sequence_2cons_leVeq x1 x2 rest h with heq | hlt
        · subst heq
          rw [nodup_sort_2cons_eq]
          exact ih (nondecreasing_sequence_cons _ _ h)
        · rw [nodup_sort_2cons_lt x1 x2 rest hlt h]
          apply nondecreasing_sequence_add_min
          · intro y hy
            have hy' : y ∈ x2 :: rest := List.mem_dedup.mp hy
            exact Nat.le_of_lt (nondecreasing_sequence_cons_smin x1 x2 rest hlt h y hy')
          · exact ih (nondecreasing_sequence_cons _ _ h)

  theorem undup_nth_le (xs : List ℕ)
      (h : nondecreasing_sequence xs) :
      nthD xs.dedup (xs.dedup.length - 2) ≤ nthD xs (xs.length - 2) := by
    induction xs with
    | nil => simp [List.dedup, nthD, List.getD]
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        simp only [List.dedup_cons, List.not_mem_nil, ↓reduceIte,
          List.dedup_nil]
        simp [nthD, List.getD]
      | cons x2 rest =>
        rcases nondecreasing_sequence_2cons_leVeq x1 x2 rest h with heq | hlt
        · -- Case x1 = x2
          subst heq  -- x1 becomes x2
          rw [nodup_sort_2cons_eq]
          have ih' := ih (nondecreasing_sequence_cons _ _ h)
          apply Nat.le_trans ih'
          -- Need: nthD (x2::rest) ((x2::rest).length - 2) ≤ nthD (x2::x2::rest) ((x2::x2::rest).length - 2)
          cases rest with
          | nil => simp [nthD, List.getD]
          | cons x3 rest' =>
            simp only [List.length_cons, nthD, List.getD]
            simp only [show List.length rest' + 1 + 1 - 2 = List.length rest' from by omega,
                       show List.length rest' + 1 + 1 + 1 - 2 = List.length rest' + 1 from by omega]
            simp only [List.getElem?_cons_succ]
            exact le_refl _
        · -- Case x1 < x2
          rw [nodup_sort_2cons_lt x1 x2 rest hlt h]
          have hnd_tail := nondecreasing_sequence_cons _ _ h
          have ih' := ih hnd_tail
          by_cases hlen : (x2 :: rest).dedup.length ≤ 1
          · -- dedup(x2::rest) has length ≤ 1
            have hdedup_pos : 0 < (x2 :: rest).dedup.length := by
              exact List.length_pos_of_mem (List.mem_dedup.mpr (List.mem_cons_self ..))
            have hdedup_eq1 : (x2 :: rest).dedup.length = 1 := by omega
            -- LHS pos: (1 + 1 - 2) = 0; LHS = nthD (x1 :: dedup) 0 = x1
            -- RHS pos: (rest.length + 2 - 2) = rest.length
            -- x1 ≤ nthD (x1::x2::rest) rest.length by nondecreasing
            show nthD (x1 :: (x2 :: rest).dedup) ((x1 :: (x2 :: rest).dedup).length - 2) ≤
                 nthD (x1 :: x2 :: rest) ((x1 :: x2 :: rest).length - 2)
            simp only [List.length_cons, hdedup_eq1]
            simp only [show 1 + 1 - 2 = 0 from by omega]
            simp only [nthD, List.getD, List.getElem?_cons_zero, Option.getD]
            -- Goal: x1 ≤ ((x1::x2::rest)[rest.length + 1 + 1 - 2]?).getD 0
            have hrest : rest.length + 1 + 1 - 2 = rest.length := by omega
            simp only [hrest]
            have hle := h 0 rest.length ⟨by omega, by simp only [List.length_cons]; omega⟩
            simp only [nthD, List.getD] at hle
            exact hle
          · push_neg at hlen
            -- dedup(x2::rest) has length ≥ 2
            show nthD (x1 :: (x2 :: rest).dedup) ((x1 :: (x2 :: rest).dedup).length - 2) ≤
                 nthD (x1 :: x2 :: rest) ((x1 :: x2 :: rest).length - 2)
            simp only [List.length_cons]
            -- LHS pos: dedup.length + 1 - 2 = dedup.length - 1
            -- Since dedup.length ≥ 2, dedup.length - 1 ≥ 1
            -- nthD (x1 :: dedup) (dedup.length - 1) = nthD dedup (dedup.length - 2)
            have hpos : (x2 :: rest).dedup.length - 1 ≥ 1 := by omega
            have hlhs : nthD (x1 :: (x2 :: rest).dedup) ((x2 :: rest).dedup.length + 1 - 2) =
                         nthD ((x2 :: rest).dedup) ((x2 :: rest).dedup.length - 2) := by
              have heq1 : (x2 :: rest).dedup.length + 1 - 2 = (x2 :: rest).dedup.length - 1 := by omega
              rw [heq1]
              simp only [nthD, List.getD]
              -- Need: (x1 :: dedup)[dedup.length - 1]?.getD 0 = dedup[dedup.length - 2]?.getD 0
              -- dedup.length - 1 ≥ 1, so (x1::dedup)[dedup.length - 1]? = dedup[dedup.length - 2]?
              have hm : (x2 :: rest).dedup.length - 1 = ((x2 :: rest).dedup.length - 2) + 1 := by omega
              rw [hm, List.getElem?_cons_succ]
            rw [hlhs]
            apply Nat.le_trans ih'
            -- nthD (x2::rest) ((x2::rest).length - 2) ≤ nthD (x1::x2::rest) (rest.length + 1 + 1 - 2)
            -- = nthD (x1::x2::rest) rest.length
            -- (x2::rest).length - 2 = rest.length + 1 - 2 = rest.length - 1
            cases rest with
            | nil =>
              simp only [List.dedup_cons, List.not_mem_nil, ↓reduceIte,
                List.dedup_nil, List.length_cons, List.length_nil] at hlen
              omega
            | cons x3 rest' =>
              simp only [List.length_cons]
              show nthD (x2 :: x3 :: rest') (rest'.length + 1 + 1 - 2) ≤
                   nthD (x1 :: x2 :: x3 :: rest') (rest'.length + 1 + 1 + 1 - 2)
              simp only [show rest'.length + 1 + 1 - 2 = rest'.length from by omega,
                         show rest'.length + 1 + 1 + 1 - 2 = rest'.length + 1 from by omega]
              simp only [nthD, List.getD, List.getElem?_cons_succ]
              exact le_refl _

end Undup

section Distances

  theorem distances_unfold_2cons (x0 x1 : ℕ) (xs : List ℕ) :
      distances (x0 :: x1 :: xs) = (x1 - x0) :: distances (x1 :: xs) := by
    simp [distances, List.drop, List.zip, List.map]

  theorem distances_unfold_2app_last (a b : ℕ) (xs : List ℕ) :
      distances (xs ++ [a, b]) = distances (xs ++ [a]) ++ [b - a] := by
    induction xs with
    | nil => simp [distances, List.drop, List.zip, List.map]
    | cons x0 tl ih =>
      cases tl with
      | nil => simp [distances, List.drop, List.zip, List.map]
      | cons x1 rest =>
        have h1 : distances ((x0 :: x1 :: rest) ++ [a, b]) = (x1 - x0) :: distances ((x1 :: rest) ++ [a, b]) := by
          simp only [List.cons_append]; rw [distances_unfold_2cons]
        have h2 : distances ((x0 :: x1 :: rest) ++ [a]) = (x1 - x0) :: distances ((x1 :: rest) ++ [a]) := by
          simp only [List.cons_append]; rw [distances_unfold_2cons]
        rw [h1, ih, h2]; simp [List.cons_append]

  theorem distances_unfold_1app_last (x : ℕ) (xs : List ℕ)
      (h : xs.length ≥ 1) :
      distances (xs ++ [x]) = distances xs ++ [x - last0 xs] := by
    induction xs with
    | nil => simp at h
    | cons x0 tl ih =>
      cases tl with
      | nil =>
        simp [distances, List.drop, List.zip, List.map, last0, List.getLastD]
      | cons x1 rest =>
        have h' : (x1 :: rest).length ≥ 1 := by simp
        have step1 : distances ((x0 :: x1 :: rest) ++ [x]) = (x1 - x0) :: distances ((x1 :: rest) ++ [x]) := by
          simp only [List.cons_append]; rw [distances_unfold_2cons]
        rw [step1, ih h', distances_unfold_2cons, List.cons_append,
            last0_cons x0 (x1 :: rest) (by simp)]

  theorem distance_between_neighboring_elements_le_max_distance_in_seq
      (xs : List ℕ) (n : ℕ) :
      nthD xs (n + 1) - nthD xs n ≤ max0 (distances xs) := by
    -- Prove nthD xs (n+1) - nthD xs n = nthD (distances xs) n by induction
    suffices h : nthD xs (n + 1) - nthD xs n = nthD (distances xs) n by
      rw [h]
      by_cases hlt : n < (distances xs).length
      · have hmem : (distances xs).getD n 0 ∈ distances xs := by
          have := List.getElem?_eq_getElem hlt
          simp [List.getD, this, List.getElem_mem]
        exact in_max0_le _ _ hmem
      · push_neg at hlt
        simp only [nthD, List.getD]
        rw [List.getElem?_eq_none (by omega)]
        simp
    -- Prove: nthD (distances xs) n = nthD xs (n+1) - nthD xs n
    -- by induction on xs
    symm
    induction xs generalizing n with
    | nil => simp [distances, nthD, List.getD]
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        cases n with
        | zero => simp [distances, nthD, List.getD, List.drop, List.zip, List.map]
        | succ m => simp [distances, nthD, List.getD, List.drop, List.zip, List.map]
      | cons x2 rest =>
        cases n with
        | zero =>
          rw [distances_unfold_2cons]
          simp [nthD, List.getD]
        | succ m =>
          rw [distances_unfold_2cons]
          show nthD ((x2 - x1) :: distances (x2 :: rest)) (m + 1) =
               nthD (x1 :: x2 :: rest) (m + 2) - nthD (x1 :: x2 :: rest) (m + 1)
          simp only [nthD, List.getD]
          simp only [List.getElem?_cons_succ]
          exact ih m

  theorem function_of_distances_is_correct (xs : List ℕ) (n : ℕ) :
      nthD (distances xs) n = nthD xs (n + 1) - nthD xs n := by
    induction xs generalizing n with
    | nil =>
      simp [distances, nthD, List.getD]
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        cases n with
        | zero => simp [distances, nthD, List.getD, List.drop, List.zip, List.map]
        | succ m => simp [distances, nthD, List.getD, List.drop, List.zip, List.map]
      | cons x2 rest =>
        cases n with
        | zero =>
          rw [distances_unfold_2cons]
          simp [nthD, List.getD]
        | succ m =>
          rw [distances_unfold_2cons]
          show nthD ((x2 - x1) :: distances (x2 :: rest)) (m + 1) =
               nthD (x1 :: x2 :: rest) (m + 2) - nthD (x1 :: x2 :: rest) (m + 1)
          simp only [nthD, List.getD]
          simp only [List.getElem?_cons_succ]
          exact ih m

  theorem size_of_seq_of_distances (xs : List ℕ)
      (h : 2 ≤ xs.length) :
      xs.length = (distances xs).length + 1 := by
    induction xs with
    | nil => simp at h
    | cons x1 tl ih =>
      cases tl with
      | nil => simp at h
      | cons x2 rest =>
        rw [distances_unfold_2cons]
        simp only [List.length_cons]
        cases rest with
        | nil =>
          simp [distances, List.drop, List.zip, List.map]
        | cons x3 rest' =>
          have h' : 2 ≤ (x2 :: x3 :: rest').length := by simp
          have := ih h'
          simp only [List.length_cons] at this ⊢
          omega

  theorem «distances_of_iota_ε» (n : ℕ) (x : ℕ)
      (h : x ∈ distances (index_iota 0 n)) :
      x = ε := by
    induction n with
    | zero =>
      simp [index_iota, distances, List.range', List.drop, List.zip, List.map] at h
    | succ m ih =>
      cases m with
      | zero =>
        simp [index_iota, distances, List.range', List.drop, List.zip, List.map] at h
      | succ k =>
        -- h : x ∈ distances (index_iota 0 (k + 1 + 1))
        -- ih : x ∈ distances (index_iota 0 (k + 1)) → x = ε
        -- Need: index_iota 0 (k+2) = index_iota 0 (k+1) ++ [k+1]
        have hlen : (index_iota 0 (k + 1)).length ≥ 1 := by
          simp [index_iota, List.length_range']
        have hiota : index_iota 0 (k + 1 + 1) = index_iota 0 (k + 1) ++ [k + 1] := by
          simp only [index_iota, Nat.sub_zero]
          have := @List.range'_append 0 (k + 1) 1 1
          simp at this; exact this.symm
        rw [hiota] at h
        rw [distances_unfold_1app_last _ _ hlen] at h
        rw [List.mem_append] at h
        rcases h with h | h
        · exact ih h
        · rw [List.mem_singleton] at h; rw [h]
          have hlast0 : last0 (index_iota 0 (k + 1)) = k := by
            -- index_iota 0 (k+1) = List.range' 0 (k+1)
            -- The last element of range' 0 (k+1) is k (for k ≥ 0, but k+1 ≥ 1 since k : ℕ)
            have hiota_k : index_iota 0 (k + 1) = index_iota 0 k ++ [k] := by
              simp only [index_iota, Nat.sub_zero]
              have := @List.range'_append 0 k 1 1
              simp at this; exact this.symm
            rw [hiota_k, last0_cat _ _ (by simp)]
            simp [last0, List.getLastD]
          omega

end Distances

section DistancesOfNonDecreasingSequence

  theorem max_distance_in_nontrivial_seq_is_positive (xs : List ℕ)
      (h1 : nondecreasing_sequence xs)
      (h2 : ∃ x y, x ∈ xs ∧ y ∈ xs ∧ x ≠ y) :
      0 < max0 (distances xs) := by
    obtain ⟨x, y, hx_in, hy_in, hne⟩ := h2
    -- WLOG x < y (or y < x)
    -- We need to find consecutive elements that differ
    -- Key lemma: if xs has two distinct elements and is nondecreasing,
    -- then there exist consecutive indices where a strict increase happens
    obtain ⟨indx, hindx, hgetx⟩ := List.mem_iff_getElem.mp hx_in
    obtain ⟨indy, hindy, hgety⟩ := List.mem_iff_getElem.mp hy_in
    -- Establish x_val = nthD xs indx, y_val = nthD xs indy
    have hx_eq : x = nthD xs indx := by
      simp only [nthD, List.getD, List.getElem?_eq_getElem hindx, Option.getD]; exact hgetx.symm
    have hy_eq : y = nthD xs indy := by
      simp only [nthD, List.getD, List.getElem?_eq_getElem hindy, Option.getD]; exact hgety.symm
    -- Suffices to show: there exist consecutive indices with strict increase
    suffices ∃ ind, ind + 1 < xs.length ∧ nthD xs ind < nthD xs (ind + 1) by
      obtain ⟨ind, hind_lt, hstrict⟩ := this
      have hpos : 0 < nthD xs (ind + 1) - nthD xs ind := by omega
      calc 0 < nthD xs (ind + 1) - nthD xs ind := hpos
        _ ≤ max0 (distances xs) := distance_between_neighboring_elements_le_max_distance_in_seq xs ind
    -- Now prove there exist consecutive indices with strict increase
    -- WLOG assume x < y (symmetric argument for y < x)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · -- x < y, so indx < indy (because nondecreasing)
      have hlt_ind : indx < indy := by
        by_contra hle
        push_neg at hle
        have := h1 indy indx ⟨hle, hindx⟩
        omega
      -- Now: between indx and indy, there must be a consecutive strict increase
      -- (telescoping: if all consecutive were equal, then xs[indx] = xs[indy], contradiction)
      -- Prove by strong induction on (indy - indx)
      have : ∃ ind, indx ≤ ind ∧ ind + 1 ≤ indy ∧ nthD xs ind < nthD xs (ind + 1) := by
        by_contra hall
        push_neg at hall
        -- All consecutive pairs in [indx, indy] are non-strictly increasing but also not strict
        -- So they're all equal, meaning xs[indx] = xs[indy]
        have heq_consec : ∀ i, indx ≤ i → i + 1 ≤ indy → nthD xs i = nthD xs (i + 1) := by
          intro i hi1 hi2
          have hle := h1 i (i + 1) ⟨by omega, by omega⟩
          have := hall i hi1 hi2
          omega
        -- By induction: xs[indx] = xs[indy]
        have heq_range : ∀ j, indx ≤ j → j ≤ indy → nthD xs indx = nthD xs j := by
          intro j hj1 hj2
          induction j with
          | zero =>
            have hzero : indx = 0 := Nat.eq_zero_of_le_zero hj1
            subst indx
            rfl
          | succ k ih =>
            rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt'
            · rfl
            · have hk_ge : indx ≤ k := by omega
              have hk_le : k ≤ indy := by omega
              rw [ih hk_ge hk_le, heq_consec k hk_ge (by omega)]
        have := heq_range indy (Nat.le_of_lt hlt_ind) (le_refl _)
        omega
      obtain ⟨ind, _, hind_le, hstrict⟩ := this
      exact ⟨ind, by omega, hstrict⟩
    · -- y < x
      have hlt_ind : indy < indx := by
        by_contra hle
        push_neg at hle
        have := h1 indx indy ⟨hle, hindy⟩
        omega
      have : ∃ ind, indy ≤ ind ∧ ind + 1 ≤ indx ∧ nthD xs ind < nthD xs (ind + 1) := by
        by_contra hall
        push_neg at hall
        have heq_consec : ∀ i, indy ≤ i → i + 1 ≤ indx → nthD xs i = nthD xs (i + 1) := by
          intro i hi1 hi2
          have hle := h1 i (i + 1) ⟨by omega, by omega⟩
          have := hall i hi1 hi2
          omega
        have heq_range : ∀ j, indy ≤ j → j ≤ indx → nthD xs indy = nthD xs j := by
          intro j hj1 hj2
          induction j with
          | zero =>
            have hzero : indy = 0 := Nat.eq_zero_of_le_zero hj1
            subst indy
            rfl
          | succ k ih =>
            rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt'
            · rfl
            · have hk_ge : indy ≤ k := by omega
              have hk_le : k ≤ indx := by omega
              rw [ih hk_ge hk_le, heq_consec k hk_ge (by omega)]
        have := heq_range indx (Nat.le_of_lt hlt_ind) (le_refl _)
        omega
      obtain ⟨ind, _, hind_le, hstrict⟩ := this
      exact ⟨ind, by omega, hstrict⟩

  theorem last_seq_minus_last_distance_seq (xs : List ℕ)
      (h : nondecreasing_sequence xs) :
      last0 xs - last0 (distances xs) = nthD xs (xs.length - 2) := by
    match xs with
    | [] => simp [last0, List.getLastD, nthD, List.getD]
    | [x1] => simp [last0, List.getLastD, distances, List.drop, List.zip, List.map, nthD, List.getD]
    | x1 :: x2 :: rest =>
      set xs := x1 :: x2 :: rest with hxs
      have hlen : 2 ≤ xs.length := by simp [hxs]
      have hsize := size_of_seq_of_distances xs hlen
      -- last0 xs = nthD xs (xs.length - 1)
      -- last0 (distances xs) = nthD (distances xs) ((distances xs).length - 1)
      --   = nthD xs ((distances xs).length) - nthD xs ((distances xs).length - 1)   [by function_of_distances_is_correct]
      -- xs.length = (distances xs).length + 1  [by size_of_seq_of_distances]
      -- So (distances xs).length = xs.length - 1
      -- last0 (distances xs) = nthD xs (xs.length - 1) - nthD xs (xs.length - 2)
      -- last0 xs - last0 (distances xs) = nthD xs (xs.length - 1) - (nthD xs (xs.length - 1) - nthD xs (xs.length - 2))
      -- = nthD xs (xs.length - 2)    [since nthD xs (xs.length - 2) ≤ nthD xs (xs.length - 1)]
      have hdlen : (distances xs).length = xs.length - 1 := by omega
      rw [last0_nth (distances xs), last0_nth xs]
      change nthD xs (xs.length - 1) -
          nthD (distances xs) ((distances xs).length - 1) =
        nthD xs (xs.length - 2)
      rw [function_of_distances_is_correct]
      have h1 : (distances xs).length - 1 = xs.length - 2 := by omega
      rw [h1]
      have h2 : xs.length - 2 + 1 = xs.length - 1 := by omega
      rw [h2]
      have hnd : nthD xs (xs.length - 2) ≤ nthD xs (xs.length - 1) := by
        apply h
        exact ⟨by omega, by omega⟩
      omega

  theorem max_distance_in_seq_le_last_element_of_seq (xs : List ℕ)
      (h : nondecreasing_sequence xs) :
      max0 (distances xs) ≤ last0 xs := by
    -- Prove: ∀ n, nthD (distances xs) n ≤ nthD (List.replicate (distances xs).length (last0 xs)) n
    -- Then max_of_dominating_seq gives: max0 (distances xs) ≤ max0 (replicate ... (last0 xs))
    -- And max0 of a constant list = that constant
    -- Simpler: use induction on xs
    induction xs with
    | nil => simp [distances, max0, last0, List.getLastD, List.drop, List.zip, List.map, List.foldl]
    | cons x1 tl ih =>
      cases tl with
      | nil => simp [distances, max0, last0, List.getLastD, List.drop, List.zip, List.map, List.foldl]
      | cons x2 rest =>
        rw [distances_unfold_2cons, max0_cons]
        rw [last0_cons x1 (x2 :: rest) (by simp)]
        apply Nat.max_le.mpr
        constructor
        · -- x2 - x1 ≤ last0 (x2 :: rest)
          have hx1 : x1 ≤ x2 := by
            have := h 0 1 ⟨by omega, by simp⟩
            simp [nthD, List.getD] at this; exact this
          have hx2_le : x2 ≤ last0 (x2 :: rest) := by
            apply last_is_max_in_nondecreasing_seq
            · exact nondecreasing_sequence_cons _ _ h
            · exact List.mem_cons_self
          omega
        · exact ih (nondecreasing_sequence_cons _ _ h)

  theorem distances_iota_filtered (xs : List ℕ) (k : ℕ)
      (h1 : ∀ x, x ∈ xs → x ≤ k)
      (h2 : nondecreasing_sequence xs) :
      distances ((index_iota 0 (k + 1)).filter (· ∈ xs)) =
      (distances xs).filter (· > 0) := by
    induction xs with
    | nil =>
      show distances ((index_iota 0 (k + 1)).filter (· ∈ ([] : List ℕ))) = List.filter (fun x => decide (x > 0)) []
      simp only [List.filter_nil]
      have : (index_iota 0 (k + 1)).filter (· ∈ ([] : List ℕ)) = [] := by
        simp [List.filter_eq_nil_iff]
      rw [this]; simp [distances, List.drop, List.zip, List.map]
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        have hx1k : x1 < k + 1 := by
          have := h1 x1 (List.mem_cons_self ..)
          omega
        rw [index_iota_filter_singl x1 0 (k + 1) ⟨by omega, hx1k⟩]
        simp [distances, List.drop, List.zip, List.map]
      | cons x2 rest =>
        have hx1k : x1 ≤ k := h1 x1 (List.mem_cons_self ..)
        have hx2k : x2 ≤ k := h1 x2 (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..)))
        have hM1 : ∀ y, y ∈ x2 :: rest → x1 ≤ y := nondecreasing_sequence_cons_min _ _ h2
        have hM2 : ∀ x, x ∈ x2 :: rest → x ≤ k := by
          intro x hx; exact h1 x (List.mem_cons.mpr (Or.inr hx))
        have hM3 : ∀ y, y ∈ rest → x2 ≤ y := by
          have := nondecreasing_sequence_cons _ _ h2
          exact nondecreasing_sequence_cons_min _ _ this
        rcases nondecreasing_sequence_2cons_leVeq x1 x2 rest h2 with heq | hlt
        · -- x1 = x2
          subst heq  -- now x2 is replaced by x1 everywhere
          rw [distances_unfold_2cons]
          simp only [Nat.sub_self]
          show distances ((index_iota 0 (k + 1)).filter (· ∈ x1 :: x1 :: rest)) =
               List.filter (fun x => decide (x > 0)) (0 :: distances (x1 :: rest))
          simp only [show ¬(0 > 0) from by omega, decide_false, Bool.false_eq_true,
                     not_false_eq_true, List.filter_cons_of_neg]
          have : (index_iota 0 (k + 1)).filter (· ∈ (x1 :: x1 :: rest)) =
                 (index_iota 0 (k + 1)).filter (· ∈ (x1 :: rest)) := by
            apply List.filter_congr
            intro y _
            simp only [List.mem_cons, decide_eq_decide]
            tauto
          rw [this]
          exact ih hM2 (nondecreasing_sequence_cons _ _ h2)
        · -- x1 < x2
          have hM4 : ∀ y, y ∈ x2 :: rest → x1 < y := nondecreasing_sequence_cons_smin x1 x2 rest hlt h2
          rw [distances_unfold_2cons]
          have hpos : x2 - x1 > 0 := by omega
          show distances ((index_iota 0 (k + 1)).filter (· ∈ x1 :: x2 :: rest)) =
               List.filter (fun x => decide (x > 0)) ((x2 - x1) :: distances (x2 :: rest))
          simp only [hpos, decide_true, List.filter_cons_of_pos]
          rw [index_iota_filter_step x1 (x2 :: rest) 0 (k + 1) ⟨by omega, by omega⟩ hM1]
          rw [rem_lt_id x1 (x2 :: rest) hM4]
          rw [index_iota_filter_step x2 rest 0 (k + 1) ⟨by omega, by omega⟩ hM3]
          rw [distances_unfold_2cons]
          congr 1
          have ih' := ih hM2 (nondecreasing_sequence_cons _ _ h2)
          rw [index_iota_filter_step x2 rest 0 (k + 1) ⟨by omega, by omega⟩ hM3] at ih'
          exact ih'

  theorem distances_positive_undup (xs : List ℕ)
      (h : nondecreasing_sequence xs) :
      (distances xs).filter (· > 0) = distances xs.dedup := by
    induction xs with
    | nil => rfl
    | cons x1 tl ih =>
      cases tl with
      | nil =>
        simp only [List.dedup_cons, List.not_mem_nil, ↓reduceIte,
          List.dedup_nil]
        simp [distances, List.drop, List.zip, List.map]
      | cons x2 rest =>
        rcases nondecreasing_sequence_2cons_leVeq x1 x2 rest h with heq | hlt
        · subst heq
          rw [distances_unfold_2cons, nodup_sort_2cons_eq]
          simp only [Nat.sub_self]
          show List.filter (fun x => decide (x > 0)) (0 :: distances (x1 :: rest)) = distances (x1 :: rest).dedup
          simp only [show ¬(0 > 0) from by omega, decide_false, Bool.false_eq_true,
                     not_false_eq_true, List.filter_cons_of_neg]
          exact ih (nondecreasing_sequence_cons _ _ h)
        · rw [distances_unfold_2cons, nodup_sort_2cons_lt x1 x2 rest hlt h]
          have hpos : x2 - x1 > 0 := by omega
          simp only [hpos, decide_true, List.filter_cons_of_pos]
          have hdedup_ne : (x2 :: rest).dedup ≠ [] := by
            intro heq
            have hmem : x2 ∈ (x2 :: rest).dedup := List.mem_dedup.mpr (List.mem_cons_self)
            rw [heq] at hmem; exact absurd hmem List.not_mem_nil
          obtain ⟨hd, tl_d, hdedup_eq⟩ := List.exists_cons_of_ne_nil hdedup_ne
          rw [hdedup_eq]
          -- Now: (x2-x1) :: filter(>0)(distances(x2::rest)) = distances(x1 :: hd :: tl_d)
          rw [distances_unfold_2cons]
          -- RHS = (hd - x1) :: distances(hd :: tl_d)
          -- We know hd = x2 since dedup of (x2::rest) starts with x2
          have hhd : hd = x2 := by
            -- The head of (x2 :: rest).dedup is x2 because the sequence is nondecreasing
            -- We prove this by showing dedup preserves the head of a nondecreasing sequence
            have hnd_tail : nondecreasing_sequence (x2 :: rest) := nondecreasing_sequence_cons _ _ h
            -- Key: (x2 :: rest).dedup = hd :: tl_d, and x2 is the min of (x2 :: rest)
            -- So x2 ≤ hd (since hd ∈ x2 :: rest) and hd ≤ x2 (since hd is first in dedup, which is nondecreasing)
            have hnd_dedup := nondecreasing_sequence_undup (x2 :: rest) hnd_tail
            rw [hdedup_eq] at hnd_dedup
            have hhd_mem : hd ∈ x2 :: rest := by
              have : hd ∈ (x2 :: rest).dedup := by rw [hdedup_eq]; exact List.mem_cons_self
              exact List.mem_dedup.mp this
            have hx2_le_hd : x2 ≤ hd := by
              rcases List.mem_cons.mp hhd_mem with rfl | hmem
              · exact le_refl _
              · exact nondecreasing_sequence_cons_min x2 rest hnd_tail hd hmem
            have hx2_mem_dedup : x2 ∈ (x2 :: rest).dedup := List.mem_dedup.mpr (List.mem_cons_self)
            rw [hdedup_eq] at hx2_mem_dedup
            have hhd_le_x2 : hd ≤ x2 := by
              rcases List.mem_cons.mp hx2_mem_dedup with heq | hmem
              · omega
              · exact nondecreasing_sequence_cons_min hd tl_d hnd_dedup x2 hmem
            omega
          subst hhd
          congr 1
          -- Goal: filter(>0)(distances(x2::rest)) = distances(x2::tl_d)
          -- We know tl_d = (rest).dedup-like... actually tl_d comes from dedup
          -- (x2::rest).dedup = x2 :: tl_d, so tl_d = tail of dedup(x2::rest)
          -- And ih says: filter(>0)(distances(x2::rest)) = distances((x2::rest).dedup)
          have ih' := ih (nondecreasing_sequence_cons _ _ h)
          rw [hdedup_eq] at ih'
          exact ih'

  theorem domination_of_distances_implies_domination_of_seq
      (xs ys : List ℕ)
      (h1 : first0 xs ≤ first0 ys)
      (h2 : 2 ≤ xs.length)
      (h3 : 2 ≤ ys.length)
      (h4 : xs.length = ys.length)
      (h5 : nondecreasing_sequence xs)
      (h6 : nondecreasing_sequence ys)
      (h7 : ∀ n, nthD (distances xs) n ≤ nthD (distances ys) n) :
      ∀ n, nthD xs n ≤ nthD ys n := by
    -- Induction on xs and ys simultaneously, peeling first elements
    match xs, ys with
    | [], _ => simp at h2
    | _, [] => simp at h3
    | [_], _ => simp at h2
    | _, [_] => simp at h3
    | x1 :: x2 :: xrest, y1 :: y2 :: yrest =>
      -- x2 ≤ y2
      have hx2y2 : x2 ≤ y2 := by
        have hx1x2 := h5 0 1 ⟨by omega, by simp⟩
        have hy1y2 := h6 0 1 ⟨by omega, by simp⟩
        simp [nthD, List.getD] at hx1x2 hy1y2
        have hd0 := h7 0
        rw [distances_unfold_2cons, distances_unfold_2cons] at hd0
        simp [nthD, List.getD] at hd0
        simp [first0, List.headD] at h1
        omega
      intro n
      cases n with
      | zero =>
        simp [nthD, List.getD, first0, List.headD] at h1 ⊢; exact h1
      | succ m =>
        simp only [nthD, List.getD, List.getElem?_cons_succ]
        -- Reduce to the tail sequences
        match xrest, yrest with
        | [], [] =>
          cases m with
          | zero => simp [List.getD]; exact hx2y2
          | succ k => simp [List.getD]
        | [], _ :: _ =>
          simp [List.length] at h4
        | _ :: _, [] =>
          simp [List.length] at h4
        | x3 :: xr, y3 :: yr =>
          -- Apply IH on (x2::x3::xr) and (y2::y3::yr)
          have h2' : 2 ≤ (x2 :: x3 :: xr).length := by simp
          have h3' : 2 ≤ (y2 :: y3 :: yr).length := by simp
          have h4' : (x2 :: x3 :: xr).length = (y2 :: y3 :: yr).length := by
            simp [List.length] at h4 ⊢; omega
          have h5' := nondecreasing_sequence_cons _ _ h5
          have h6' := nondecreasing_sequence_cons _ _ h6
          have h1' : first0 (x2 :: x3 :: xr) ≤ first0 (y2 :: y3 :: yr) := by
            simp [first0, List.headD]; exact hx2y2
          have h7' : ∀ n, nthD (distances (x2 :: x3 :: xr)) n ≤ nthD (distances (y2 :: y3 :: yr)) n := by
            intro k
            have := h7 (k + 1)
            rw [distances_unfold_2cons, distances_unfold_2cons] at this
            simp only [nthD, List.getD, List.getElem?_cons_succ] at this
            exact this
          have := domination_of_distances_implies_domination_of_seq
                    (x2 :: x3 :: xr) (y2 :: y3 :: yr) h1' h2' h3' h4' h5' h6' h7' m
          exact this

end DistancesOfNonDecreasingSequence

end NondecreasingSequence

end Prosa.Util.Nondecreasing
