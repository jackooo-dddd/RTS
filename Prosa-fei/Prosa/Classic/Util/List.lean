-- Translated from: ../rt-proofs/classic/util/list.v
import Mathlib
import Prosa.Util.List
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.List

open List

section UniqList

  theorem idx_lt_rcons {T : Type _} [DecidableEq T] (l : List T) (i : ℕ) (x0 : T)
      (h1 : l.Nodup) (h2 : i < l.length) :
      l.filter (fun x => decide (l.idxOf x < i + 1)) =
        (l.filter (fun x => decide (l.idxOf x < i))) ++ [l.getD i x0] := by
    -- Local helper: in a nodup list, filter by idxOf < k = take k
    suffices filter_eq_take : ∀ (l' : List T) (k : ℕ), l'.Nodup → k ≤ l'.length →
        l'.filter (fun x => decide (l'.idxOf x < k)) = l'.take k by
      rw [filter_eq_take l (i + 1) h1 (by omega), filter_eq_take l i h1 (by omega)]
      rw [List.getD_eq_getElem l x0 h2]
      rw [List.take_succ]
      simp [show l[i]? = some l[i] from List.getElem?_eq_getElem h2]
    intro l' k hnd hk
    induction l' generalizing k with
    | nil => simp at hk; simp [hk]
    | cons a tl ih =>
      rw [List.nodup_cons] at hnd
      cases k with
      | zero =>
        simp only [List.take_zero]
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp only [decide_eq_true_eq, not_lt, Nat.le_zero]
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [List.idxOf_cons]
        · simp only [List.idxOf_cons]
          have hne : (a == x) = false := by
            simp [beq_eq_decide]; intro heq; exact hnd.1 (heq ▸ hx)
          simp only [hne, cond_false]
          omega
      | succ n =>
        simp only [List.filter_cons, List.take_succ_cons]
        have hdec : decide (List.idxOf a (a :: tl) < n + 1) = true := by
          simp only [List.idxOf_cons, beq_self_eq_true, cond_true, decide_eq_true_eq]
          omega
        rw [hdec]; simp only [ite_true]
        congr 1
        have htl_filter : tl.filter (fun x => decide (List.idxOf x (a :: tl) < n + 1)) =
            tl.filter (fun x => decide (tl.idxOf x < n)) := by
          apply List.filter_congr
          intro x hx
          simp only [List.idxOf_cons, decide_eq_decide]
          have hne : (a == x) = false := by
            simp [beq_eq_decide]; intro heq; exact hnd.1 (heq ▸ hx)
          simp only [hne, cond_false]
          omega
        rw [htl_filter]
        exact ih n hnd.2 (by simp at hk; omega)

  theorem filter_idx_lt_take {T : Type _} [DecidableEq T] (l : List T) (i : ℕ)
      (h1 : l.Nodup) (h2 : i < l.length) :
      l.filter (fun x => decide (l.idxOf x < i)) = l.take i := by
    induction l generalizing i with
    | nil => simp at h2
    | cons a tl ih =>
      rw [List.nodup_cons] at h1
      obtain ⟨ha_notin, htl_nodup⟩ := h1
      cases i with
      | zero =>
        simp only [List.take_zero]
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp only [decide_eq_true_eq, not_lt, Nat.le_zero]
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [List.idxOf_cons]
        · simp only [List.idxOf_cons]
          have hne : (a == x) = false := by
            simp [beq_eq_decide]; intro heq; exact ha_notin (heq ▸ hx)
          simp only [hne, cond_false]
          omega
      | succ n =>
        simp only [List.filter_cons, List.take_succ_cons]
        have hdec : decide (List.idxOf a (a :: tl) < n + 1) = true := by
          simp only [List.idxOf_cons, beq_self_eq_true, cond_true, decide_eq_true_eq]
          omega
        rw [hdec]; simp only [ite_true]
        congr 1
        have htl_filter : tl.filter (fun x => decide (List.idxOf x (a :: tl) < n + 1)) =
            tl.filter (fun x => decide (tl.idxOf x < n)) := by
          apply List.filter_congr
          intro x hx
          simp only [List.idxOf_cons, decide_eq_decide]
          have hne : (a == x) = false := by
            simp [beq_eq_decide]; intro heq; exact ha_notin (heq ▸ hx)
          simp only [hne, cond_false]
          omega
        rw [htl_filter]
        exact ih n htl_nodup (by simp at h2; omega)

  theorem filter_idx_le_takeS {T : Type _} [DecidableEq T] (l : List T) (i : ℕ)
      (h1 : l.Nodup) (h2 : i < l.length) :
      l.filter (fun x => decide (l.idxOf x ≤ i)) = l.take (i + 1) := by
    have heq : (fun x => decide (l.idxOf x ≤ i)) = (fun x => decide (l.idxOf x < i + 1)) := by
      ext x; simp only [decide_eq_decide]; omega
    rw [heq]
    -- Use idx_lt_rcons' proof strategy: induction on l generalizing i+1
    -- since filter_idx_lt_take requires strict < length, we inline the proof for ≤ length
    induction l generalizing i with
    | nil => simp at h2
    | cons a tl ih =>
      rw [List.nodup_cons] at h1
      obtain ⟨ha_notin, htl_nodup⟩ := h1
      simp only [List.filter_cons, List.take_succ_cons]
      have hdec : decide (List.idxOf a (a :: tl) < i + 1) = true := by
        simp only [List.idxOf_cons, beq_self_eq_true, cond_true, decide_eq_true_eq]
        omega
      rw [hdec]; simp only [ite_true]
      congr 1
      have htl_filter : tl.filter (fun x => decide (List.idxOf x (a :: tl) < i + 1)) =
          tl.filter (fun x => decide (tl.idxOf x < i)) := by
        apply List.filter_congr
        intro x hx
        simp only [List.idxOf_cons, decide_eq_decide]
        have hne : (a == x) = false := by
          simp [beq_eq_decide]; intro heq'; exact ha_notin (heq' ▸ hx)
        simp only [hne, cond_false]
        omega
      rw [htl_filter]
      by_cases hi : i < tl.length
      · exact filter_idx_lt_take tl i htl_nodup hi
      · -- i ≥ tl.length, so take i tl = tl and filter should also be tl
        have hle : tl.length ≤ i := by omega
        rw [List.take_of_length_le hle]
        rw [List.filter_eq_self]
        intro x hx
        simp only [decide_eq_true_eq]
        exact Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hx) hle

  theorem mapP2 (T : Type _) (T' : Type _) [DecidableEq T'] (s : List T) (f : T → T') (y : T') :
      y ∈ s.map f ↔ ∃ x, x ∈ s ∧ y = f x := by
    constructor
    · intro h
      rw [List.mem_map] at h
      obtain ⟨x, hx, hfx⟩ := h
      exact ⟨x, hx, hfx.symm⟩
    · intro ⟨x, hx, hfx⟩
      rw [List.mem_map]
      exact ⟨x, hx, hfx.symm⟩

end UniqList

section Zip

  theorem zipP {T : Type _} [DecidableEq T] (x0 : T) (P : T → T → Bool) (X Y : List T)
      (h : X.length = Y.length) :
      (∀ i, i < (X.zip Y).length → P (X.getD i x0) (Y.getD i x0) = true) ↔
        (X.zip Y).Forall (fun p => P p.1 p.2 = true) := by
    have hlen : (X.zip Y).length = X.length := by simp [List.length_zip, h]
    constructor
    · intro hall
      rw [List.forall_iff_forall_mem]
      intro p hp
      rw [List.mem_iff_getElem] at hp
      obtain ⟨idx, hidx, hget⟩ := hp
      have hi1 : idx < X.length := by omega
      have hi2 : idx < Y.length := by omega
      have := hall idx hidx
      rw [List.getD_eq_getElem X x0 hi1, List.getD_eq_getElem Y x0 hi2] at this
      have hzip : (X.zip Y)[idx] = (X[idx]'hi1, Y[idx]'hi2) := List.getElem_zip
      rw [hzip] at hget; rw [← hget]; exact this
    · intro hall i hi
      rw [List.forall_iff_forall_mem] at hall
      have hi1 : i < X.length := by omega
      have hi2 : i < Y.length := by omega
      rw [List.getD_eq_getElem X x0 hi1, List.getD_eq_getElem Y x0 hi2]
      have hmem : (X.zip Y)[i] ∈ X.zip Y := List.getElem_mem hi
      have hzip : (X.zip Y)[i] = (X[i]'hi1, Y[i]'hi2) := List.getElem_zip
      have := hall _ hmem
      rw [hzip] at this; exact this

  theorem mem_zip_exists (T T' : Type _) [DecidableEq T] [DecidableEq T']
      (x1 : T) (x2 : T') (l1 : List T) (l2 : List T') (elem : T) (elem' : T')
      (h1 : l1.length = l2.length) (h2 : (x1, x2) ∈ l1.zip l2) :
      ∃ idx, idx < l1.length ∧ idx < l2.length ∧
        x1 = l1.getD idx elem ∧ x2 = l2.getD idx elem' := by
    rw [List.mem_iff_getElem] at h2
    obtain ⟨i, hi, hget⟩ := h2
    have hlen : (l1.zip l2).length = l1.length := by simp [List.length_zip, h1]
    have hi1 : i < l1.length := by omega
    have hi2 : i < l2.length := by omega
    have hzip : (l1.zip l2)[i] = (l1[i]'hi1, l2[i]'hi2) := List.getElem_zip
    rw [hzip] at hget
    refine ⟨i, hi1, hi2, ?_, ?_⟩
    · rw [List.getD_eq_getElem l1 elem hi1]; exact (Prod.mk.inj hget).1.symm
    · rw [List.getD_eq_getElem l2 elem' hi2]; exact (Prod.mk.inj hget).2.symm

  theorem mem_zip (T T' : Type _) [DecidableEq T] [DecidableEq T']
      (x1 : T) (x2 : T') (l1 : List T) (l2 : List T')
      (h1 : l1.length = l2.length) (h2 : (x1, x2) ∈ l1.zip l2) :
      x1 ∈ l1 ∧ x2 ∈ l2 := by
    rw [List.mem_iff_getElem] at h2
    obtain ⟨i, hi, hget⟩ := h2
    have hi1 : i < l1.length := by simp [List.length_zip, h1] at hi; omega
    have hi2 : i < l2.length := by simp [List.length_zip, h1] at hi; omega
    have hzip : (l1.zip l2)[i] = (l1[i]'hi1, l2[i]'hi2) := List.getElem_zip
    rw [hzip] at hget
    obtain ⟨h1eq, h2eq⟩ := Prod.mk.inj hget
    exact ⟨h1eq ▸ List.getElem_mem hi1, h2eq ▸ List.getElem_mem hi2⟩

  theorem mem_zip_nseq_r {T1 T2 : Type _} [DecidableEq T1] [DecidableEq T2]
      (x : T1) (y : T2) (n : ℕ) (l : List T1)
      (h : l.length = n) :
      (x, y) ∈ l.zip (List.replicate n y) ↔ x ∈ l := by
    subst h
    constructor
    · intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨i, hi, hget⟩ := hmem
      have hi1 : i < l.length := by simp [List.length_zip] at hi; omega
      have hzip : (l.zip (List.replicate l.length y))[i] = (l[i]'hi1, (List.replicate l.length y)[i]'(by simp; omega)) := List.getElem_zip
      rw [hzip] at hget
      exact (Prod.mk.inj hget).1 ▸ List.getElem_mem hi1
    · intro hmem
      induction l with
      | nil => simp at hmem
      | cons a tl ih =>
        simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons] at *
        rcases hmem with rfl | hmem
        · left; rfl
        · right; exact ih hmem

  theorem mem_zip_nseq_l {T1 T2 : Type _} [DecidableEq T1] [DecidableEq T2]
      (x : T1) (y : T2) (n : ℕ) (l : List T2)
      (h : l.length = n) :
      (x, y) ∈ (List.replicate n x).zip l ↔ y ∈ l := by
    subst h
    constructor
    · intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨i, hi, hget⟩ := hmem
      have hi1 : i < l.length := by simp [List.length_zip] at hi; omega
      have hzip : ((List.replicate l.length x).zip l)[i] = ((List.replicate l.length x)[i]'(by simp; omega), l[i]'hi1) := List.getElem_zip
      rw [hzip] at hget
      exact (Prod.mk.inj hget).2 ▸ List.getElem_mem hi1
    · intro hmem
      induction l with
      | nil => simp at hmem
      | cons a tl ih =>
        simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons] at *
        rcases hmem with rfl | hmem
        · left; rfl
        · right; exact ih hmem

  theorem unzip1_pair {T1 T2 : Type _} (l : List T1) (f : T1 → T2) :
      (l.map (fun x => (x, f x))).unzip.1 = l := by
    rw [List.unzip_fst, List.map_map]
    simp [Function.comp_def]

  theorem unzip2_pair {T1 T2 : Type _} (l : List T1) (f : T1 → T2) :
      (l.map (fun x => (f x, x))).unzip.2 = l := by
    rw [List.unzip_snd, List.map_map]
    simp [Function.comp_def]

  theorem eq_unzip1 {T1 T2 : Type _}
      (l1 l2 : List (T1 × T2)) (x0 : T1 × T2)
      (h1 : l1.length = l2.length)
      (h2 : ∀ i, i < l1.length → (l1.getD i x0).1 = (l2.getD i x0).1) :
      l1.unzip.1 = l2.unzip.1 := by
    rw [List.unzip_fst, List.unzip_fst]
    apply List.ext_getElem
    · simp; exact h1
    · intro i hi1 hi2
      simp only [List.getElem_map]
      have hi1' : i < l1.length := by simpa using hi1
      have := h2 i hi1'
      rw [List.getD_eq_getElem l1 x0 hi1', List.getD_eq_getElem l2 x0 (by omega)] at this
      exact this

  theorem eq_unzip2 {T1 T2 : Type _}
      (l1 l2 : List (T1 × T2)) (x0 : T1 × T2)
      (h1 : l1.length = l2.length)
      (h2 : ∀ i, i < l1.length → (l1.getD i x0).2 = (l2.getD i x0).2) :
      l1.unzip.2 = l2.unzip.2 := by
    rw [List.unzip_snd, List.unzip_snd]
    apply List.ext_getElem
    · simp; exact h1
    · intro i hi1 hi2
      simp only [List.getElem_map]
      have hi1' : i < l1.length := by simpa using hi1
      have := h2 i hi1'
      rw [List.getD_eq_getElem l1 x0 hi1', List.getD_eq_getElem l2 x0 (by omega)] at this
      exact this

end Zip

def nth_or_none {T : Type _} (l : List T) (n : ℕ) : Option T :=
  l[n]?

section Nth

  variable {T : Type _} [DecidableEq T]

  theorem nth_in_or_default (l : List T) (x0 : T) (i : ℕ) :
      l.getD i x0 ∈ l ∨ l.getD i x0 = x0 := by
    by_cases h : i < l.length
    · left
      rw [List.getD_eq_getElem l x0 h]
      exact List.getElem_mem h
    · right
      push_neg at h
      exact List.getD_eq_default l x0 h

  theorem nth_neq_default (l : List T) (x0 : T) (i : ℕ) (y : T)
      (h1 : l.getD i x0 = y) (h2 : y ≠ x0) :
      y ∈ l := by
    have := nth_in_or_default l x0 i
    rw [h1] at this
    exact this.resolve_right h2

  theorem nth_or_none_mem (l : List T) (n : ℕ) (x : T)
      (h : nth_or_none l n = some x) :
      x ∈ l := by
    simp only [nth_or_none] at h
    obtain ⟨hn, hx⟩ := List.getElem?_eq_some_iff.mp h
    rw [← hx]; exact List.getElem_mem hn

  theorem nth_or_none_mem_exists (l : List T) (x : T)
      (h : x ∈ l) :
      ∃ n, nth_or_none l n = some x := by
    simp only [nth_or_none]
    rw [List.mem_iff_getElem] at h
    obtain ⟨i, hi, hx⟩ := h
    exact ⟨i, List.getElem?_eq_some_iff.mpr ⟨hi, hx⟩⟩

  theorem nth_or_none_size_none (l : List T) (n : ℕ) :
      nth_or_none l n = none ↔ n ≥ l.length := by
    simp [nth_or_none]

  theorem nth_or_none_size_some (l : List T) (n : ℕ) (x : T)
      (h : nth_or_none l n = some x) :
      n < l.length := by
    simp only [nth_or_none] at h
    exact (List.getElem?_eq_some_iff.mp h).1

  theorem nth_or_none_uniq (l : List T) (i j : ℕ) (x : T)
      (h1 : l.Nodup) (h2 : nth_or_none l i = some x)
      (h3 : nth_or_none l j = some x) :
      i = j := by
    simp only [nth_or_none] at h2 h3
    obtain ⟨hi, hxi⟩ := List.getElem?_eq_some_iff.mp h2
    obtain ⟨hj, hxj⟩ := List.getElem?_eq_some_iff.mp h3
    have : l[i] = l[j] := by rw [hxi, hxj]
    exact (List.Nodup.getElem_inj_iff h1).mp this

  theorem nth_or_none_nth (l : List T) (n : ℕ) (x : T) (x0 : T)
      (h : nth_or_none l n = some x) :
      l.getD n x0 = x := by
    simp only [nth_or_none] at h
    obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp h
    rw [List.getD_eq_getElem l x0 hlt]
    exact hx

end Nth

section PartialMap

  theorem pmap_inj_in_uniq {T T' : Type _} [DecidableEq T] [DecidableEq T']
      (s : List T) (f : T → Option T')
      (h1 : ∀ a b, a ∈ s → b ∈ s → f a = f b → a = b)
      (h2 : s.Nodup) :
      (s.filterMap f).Nodup := by
    induction s with
    | nil => simp
    | cons a tl ih =>
      simp only [List.filterMap_cons]
      have hnodup_tl : tl.Nodup := (List.nodup_cons.mp h2).2
      have hnotin : a ∉ tl := (List.nodup_cons.mp h2).1
      have ih' : (tl.filterMap f).Nodup := ih
          (fun x y hx hy hfxy => h1 x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy) hfxy)
          hnodup_tl
      cases hfa : f a with
      | none => simpa [hfa]
      | some val =>
        simp only [hfa]
        exact List.nodup_cons.mpr ⟨fun hmem => by
          rw [List.mem_filterMap] at hmem
          obtain ⟨b, hb_mem, hb_eq⟩ := hmem
          have : a = b := h1 a b List.mem_cons_self (List.mem_cons_of_mem _ hb_mem) (by rw [hfa, hb_eq])
          exact hnotin (this ▸ hb_mem), ih'⟩

  theorem pmap_inj_uniq {T T' : Type _} [DecidableEq T] [DecidableEq T']
      (s : List T) (f : T → Option T')
      (h1 : Function.Injective f)
      (h2 : s.Nodup) :
      (s.filterMap f).Nodup := by
    apply pmap_inj_in_uniq
    · intro a b _ _ hab; exact h1 hab
    · exact h2

end PartialMap

def set_nth_if_exists {T : Type _} (l : List T) (n : ℕ) (y : T) : List T :=
  if n < l.length then l.set n y else l

def replace_first {T : Type _} (P : T → Bool) (f : T → T) : List T → List T
  | [] => []
  | x0 :: l' => if P x0 then f x0 :: l' else x0 :: replace_first P f l'

def replace_first_const {T : Type _} (P : T → Bool) (y : T) (l : List T) : List T :=
  replace_first P (fun _ => y) l

def set_pair_1nd {T1 T2 : Type _} (y : T2) (p : T1 × T2) : T1 × T2 :=
  (p.1, y)

def set_pair_2nd {T1 T2 : Type _} (y : T2) (p : T1 × T2) : T1 × T2 :=
  (p.1, y)

section Replace

  variable {T : Type _} [DecidableEq T]

  theorem replace_first_size (P : T → Bool) (f : T → T) (l : List T) :
      (replace_first P f l).length = l.length := by
    induction l with
    | nil => simp [replace_first]
    | cons a tl ih =>
      simp only [replace_first]
      split <;> simp [ih]

  theorem replace_first_cases {P : T → Bool} {f : T → T} {l : List T} {x : T}
      (h : x ∈ replace_first P f l) :
      x ∈ l ∨ (∃ y, x = f y ∧ P y = true ∧ y ∈ l) := by
    induction l with
    | nil => simp [replace_first] at h
    | cons a tl ih =>
      simp only [replace_first] at h
      by_cases hpa : P a = true
      · simp [hpa] at h
        rcases h with rfl | h
        · right; exact ⟨a, rfl, hpa, List.mem_cons_self⟩
        · left; exact List.mem_cons_of_mem _ h
      · simp [show ¬(P a = true) from hpa] at h
        rcases h with rfl | h
        · left; exact List.mem_cons_self
        · rcases ih h with h' | ⟨y, hxy, hpy, hym⟩
          · left; exact List.mem_cons_of_mem _ h'
          · right; exact ⟨y, hxy, hpy, List.mem_cons_of_mem _ hym⟩

  theorem replace_first_no_change {P : T → Bool} {f : T → T} {l : List T} {x : T}
      (h1 : x ∈ l) (h2 : P x = false) :
      x ∈ replace_first P f l := by
    induction l with
    | nil => simp at h1
    | cons a tl ih =>
      simp only [replace_first]
      by_cases hpa : P a = true
      · simp [hpa]
        rcases List.mem_cons.mp h1 with rfl | h
        · simp [h2] at hpa
        · right; exact h
      · simp [show ¬(P a = true) from hpa]
        rcases List.mem_cons.mp h1 with rfl | h
        · left; rfl
        · right; exact ih h

  theorem replace_first_idempotent {P : T → Bool} {f : T → T} {l : List T} {x : T}
      (h1 : x ∈ l) (h2 : f x = x) :
      x ∈ replace_first P f l := by
    induction l with
    | nil => simp at h1
    | cons a tl ih =>
      simp only [replace_first]
      by_cases hpa : P a = true
      · simp [hpa]
        rcases List.mem_cons.mp h1 with rfl | h
        · left; exact h2.symm
        · right; exact h
      · simp [show ¬(P a = true) from hpa]
        rcases List.mem_cons.mp h1 with rfl | h
        · left; rfl
        · right; exact ih h

  theorem replace_first_new (P : T → Bool) (f : T → T) (l : List T) (x1 x2 : T)
      (h1 : x1 ∉ l) (h2 : x2 ∉ l)
      (h3 : x1 ∈ replace_first P f l) (h4 : x2 ∈ replace_first P f l) :
      x1 = x2 := by
    induction l with
    | nil => simp [replace_first] at h3
    | cons a tl ih =>
      simp only [replace_first] at h3 h4
      rw [List.mem_cons] at h1 h2
      push_neg at h1 h2
      by_cases hpa : P a = true
      · simp [hpa] at h3 h4
        rcases h3 with rfl | h3
        · rcases h4 with rfl | h4
          · rfl
          · exact absurd h4 h2.2
        · exact absurd h3 h1.2
      · simp [show ¬(P a = true) from hpa] at h3 h4
        rcases h3 with rfl | h3
        · exact absurd rfl h1.1
        · rcases h4 with rfl | h4
          · exact absurd rfl h2.1
          · exact ih h1.2 h2.2 h3 h4

  theorem replace_first_previous {P : T → Bool} {f : T → T} {l : List T} {x : T}
      (h : x ∈ l) :
      (x ∈ replace_first P f l) ∨
      (P x = true ∧ f x ∈ replace_first P f l) := by
    induction l with
    | nil => simp at h
    | cons a tl ih =>
      simp only [replace_first]
      by_cases hpa : P a = true
      · simp [hpa]
        rcases List.mem_cons.mp h with rfl | h
        · right; exact ⟨hpa, Or.inl rfl⟩
        · left; right; exact h
      · simp [show ¬(P a = true) from hpa]
        rcases List.mem_cons.mp h with rfl | h
        · left; left; rfl
        · rcases ih h with h' | ⟨hpx, hfx⟩
          · left; right; exact h'
          · right; exact ⟨hpx, Or.inr hfx⟩

  theorem replace_first_failed {P : T → Bool} {f : T → T} {l : List T}
      (h : ∀ x, x ∈ l → f x ∉ replace_first P f l) :
      ∀ x, x ∈ l → P x = false := by
    induction l with
    | nil => intro x; simp
    | cons a tl ih =>
      intro x hx
      by_cases hpa : P a = true
      · -- P a = true, so replace_first gives f a :: tl
        exfalso
        have ha_mem : a ∈ a :: tl := List.mem_cons_self
        have hfa_notin := h a ha_mem
        simp only [replace_first] at hfa_notin
        rw [if_pos hpa] at hfa_notin
        apply hfa_notin
        exact List.mem_cons_self
      · -- P a = false
        simp only [Bool.not_eq_true] at hpa
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hpa
        · apply ih _ x hx'
          intro y hy
          have hfy_notin := h y (List.mem_cons_of_mem _ hy)
          simp only [replace_first] at hfy_notin
          rw [if_neg (by simp [hpa])] at hfy_notin
          rw [List.mem_cons] at hfy_notin
          push_neg at hfy_notin
          exact hfy_notin.2

end Replace

def pairs_to_function {T1 : Type _} [DecidableEq T1] {T2 : Type _} (y0 : T2)
    (l : List (T1 × T2)) : T1 → T2 :=
  fun x => (l.unzip.2).getD (l.unzip.1.idxOf x) y0

section Pairs

  theorem pairs_to_function_neq_default {T1 : Type _} [DecidableEq T1]
      {T2 : Type _} [DecidableEq T2]
      (y0 : T2) (l : List (T1 × T2)) (x : T1) (y : T2)
      (h1 : pairs_to_function y0 l x = y) (h2 : y ≠ y0) :
      (x, y) ∈ l := by
    induction l with
    | nil =>
      simp [pairs_to_function, List.unzip_snd, List.unzip_fst] at h1
      exact absurd h1.symm h2
    | cons a tl ih =>
      simp only [pairs_to_function, List.unzip_snd, List.unzip_fst, List.map_cons, List.idxOf_cons] at h1
      by_cases hfst : a.1 = x
      · rw [show (a.1 == x) = true from beq_iff_eq.mpr hfst] at h1
        simp at h1
        rw [← h1]
        exact List.mem_cons.mpr (Or.inl (Prod.ext hfst.symm rfl))
      · rw [show (a.1 == x) = false from by simp [beq_eq_decide]; exact hfst] at h1
        simp at h1
        have ih_input : pairs_to_function y0 tl x = y := by
          simp [pairs_to_function, List.unzip_snd, List.unzip_fst]
          exact h1
        exact List.mem_cons_of_mem _ (ih ih_input)

  theorem pairs_to_function_mem {T1 : Type _} [DecidableEq T1]
      {T2 : Type _} [DecidableEq T2]
      (y0 : T2) (l : List (T1 × T2)) (x : T1) (y : T2)
      (h1 : (l.unzip.1).Nodup) (h2 : (x, y) ∈ l) :
      pairs_to_function y0 l x = y := by
    induction l with
    | nil => simp at h2
    | cons a tl ih =>
      simp only [pairs_to_function, List.unzip_snd, List.unzip_fst, List.map_cons, List.idxOf_cons]
      rw [List.unzip_fst, List.map_cons, List.nodup_cons] at h1
      obtain ⟨hnotin, hnodup_tl⟩ := h1
      by_cases hfst : a.1 = x
      · rw [show (a.1 == x) = true from beq_iff_eq.mpr hfst]
        simp
        rcases List.mem_cons.mp h2 with heq | hmem
        · exact (congrArg Prod.snd heq).symm
        · exfalso; apply hnotin
          rw [hfst]
          exact List.mem_map.mpr ⟨(x, y), hmem, rfl⟩
      · rw [show (a.1 == x) = false from by simp [beq_eq_decide]; exact hfst]
        simp
        rcases List.mem_cons.mp h2 with heq | hmem
        · exfalso; apply hfst; exact (congrArg Prod.fst heq).symm
        · have hih := ih (by rw [List.unzip_fst]; exact hnodup_tl) hmem
          simp [pairs_to_function, List.unzip_snd, List.unzip_fst] at hih
          exact hih

end Pairs

section Order

  variable {T : Type _} [DecidableEq T]
  variable (rel : T → T → Bool)
  variable (l : List T)

  def total_over_list : Prop :=
    ∀ x1 x2, x1 ∈ l → x2 ∈ l → (rel x1 x2 = true ∨ rel x2 x1 = true)

  def antisymmetric_over_list : Prop :=
    ∀ x1 x2, x1 ∈ l → x2 ∈ l → rel x1 x2 = true → rel x2 x1 = true → x1 = x2

end Order

section AdditionalLemmas

  theorem in_cat {X : Type _} [DecidableEq X] (x : X) (xs : List X)
      (h : x ∈ xs) :
      ∃ xsl xsr, xs = xsl ++ [x] ++ xsr := by
    induction xs with
    | nil => simp at h
    | cons a tl ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact ⟨[], tl, by simp⟩
      · obtain ⟨xsl, xsr, hxs⟩ := ih hmem
        exact ⟨a :: xsl, xsr, by simp [hxs]⟩

  private def seq_max : List ℕ → ℕ := List.foldl Nat.max 0

  theorem seq_max_cons (x : ℕ) (xs : List ℕ) :
      seq_max (x :: xs) = Nat.max x (seq_max xs) := by
    suffices h : ∀ (s : ℕ) (y : ℕ) (ys : List ℕ),
        List.foldl Nat.max s (y :: ys) = Nat.max y (List.foldl Nat.max s ys) by
      exact h 0 x xs
    intro s y ys
    revert s y
    induction ys with
    | nil =>
      intro s y
      simp only [List.foldl]
      exact Nat.max_comm s y
    | cons a tl ih =>
      intro s y
      simp only [List.foldl]
      have hsya : Nat.max (Nat.max s y) a = Nat.max (Nat.max s a) y := by
        simp [Nat.max_assoc, Nat.max_comm y a]
      rw [hsya]
      have := ih (Nat.max s a) y
      simp only [List.foldl] at this
      exact this

  theorem subseq_leq_size {X : Type _} [DecidableEq X] (xs ys : List X)
      (h1 : xs.Nodup) (h2 : ∀ x, x ∈ xs → x ∈ ys) :
      xs.length ≤ ys.length := by
    have hsub : xs.toFinset ⊆ ys.toFinset := by
      intro x; simp only [List.mem_toFinset]; exact h2 x
    calc xs.length = xs.toFinset.card :=
            (List.toFinset_card_of_nodup h1).symm
      _ ≤ ys.toFinset.card := Finset.card_le_card hsub
      _ ≤ ys.length := List.toFinset_card_le ys

end AdditionalLemmas

end Prosa.Classic.Util.List
