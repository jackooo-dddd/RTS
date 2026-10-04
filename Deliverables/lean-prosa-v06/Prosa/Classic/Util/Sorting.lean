-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/sorting.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 17)

import Prosa.Classic.Util.Induction
import Prosa.Classic.Util.List
import Mathlib.Data.List.Chain

/-!
Lemmas about sorted sequences.

Representation notes:
* MathComp's `sorted leT xs` relates adjacent elements; as in the accepted v0.6
  translation it is `List.IsChain (fun a b => leT a b = true) xs`.
* `rel T` is `T → T → Bool`; `transitive leT` is MathComp's
  `∀ y x z, leT x y → leT y z → leT x z`, kept with the same binder order.
* The section variables `T`, `leT`, `xs`, `default` and the transitivity
  hypothesis become leading arguments in declaration order, only where used
  (as Rocq abstracts them when the section is closed).
* The section-local `nth := nth default` is `List.getD · · default`;
  `(size xs).-1` is `xs.length - 1`.
* `def` is a Lean keyword, so the source binder `def` is written `«def»`.
-/

namespace Prosa.Classic.Util.Sorting

open Prosa.Classic.Util.List (antisymmetric_over_list)

universe u

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt {α : Type u} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- LEAN_HELPER: in a chain of a transitive relation, earlier elements are related
to later ones. -/
private theorem chain_rel_of_lt {T : Type u} (R : T → T → Prop)
    (trans : ∀ y x z, R x y → R y z → R x z) (l : List T) (h : List.IsChain R l) :
    ∀ j i (hij : i < j) (hj : j < l.length), R (l[i]'(by omega)) l[j] := by
  intro j
  induction j with
  | zero => intro i hij; omega
  | succ j ih =>
      intro i hij hj
      have step : R l[j] l[j + 1] := h.getElem j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
      · exact trans _ _ _ (ih i hlt (by omega)) step
      · subst heq; exact step

theorem sort_ordered (T : Type u) [DecidableEq T] (leT : T → T → Bool) (xs : List T)
    (default : T) :
    ∀ idx : Nat,
      List.IsChain (fun a b => leT a b = true) xs →
      idx < xs.length - 1 →
      leT (xs.getD idx default) (xs.getD (idx + 1) default) = true := by
  intro idx SORT LT
  rw [getD_lt (by omega), getD_lt (by omega)]
  exact SORT.getElem idx (by omega)

theorem sorted_rcons_prefix (T : Type u) [DecidableEq T] (leT : T → T → Bool)
    (xs : List T) :
    ∀ x : T,
      List.IsChain (fun a b => leT a b = true) (xs ++ [x]) →
      List.IsChain (fun a b => leT a b = true) xs := by
  intro x SORT
  exact (List.isChain_append.mp SORT).1

theorem order_sorted_rcons (T : Type u) [DecidableEq T] (leT : T → T → Bool)
    (xs : List T)
    (H_leT_is_transitive : ∀ y x z, leT x y = true → leT y z = true → leT x z = true) :
    ∀ x lst : T,
      List.IsChain (fun a b => leT a b = true) (xs ++ [lst]) →
      x ∈ xs →
      leT x lst = true := by
  intro x lst SORT IN
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem IN
  have h := chain_rel_of_lt _ H_leT_is_transitive _ SORT xs.length i hi (by simp)
  simpa [List.getElem_append_left hi] using h

theorem sorted_lt_idx_implies_rel (T : Type u) [DecidableEq T] (leT : T → T → Bool)
    (xs : List T) (default : T)
    (H_leT_is_transitive : ∀ y x z, leT x y = true → leT y z = true → leT x z = true) :
    ∀ i1 i2 : Nat,
      List.IsChain (fun a b => leT a b = true) xs →
      i1 < i2 →
      i2 < xs.length →
      leT (xs.getD i1 default) (xs.getD i2 default) = true := by
  intro i1 i2 SORT LE LEsize
  rw [getD_lt (by omega), getD_lt LEsize]
  exact chain_rel_of_lt _ H_leT_is_transitive _ SORT i2 i1 LE LEsize

theorem sorted_rel_implies_le_idx (T : Type u) [DecidableEq T] (leT : T → T → Bool)
    (xs : List T) (default : T)
    (H_leT_is_transitive : ∀ y x z, leT x y = true → leT y z = true → leT x z = true) :
    ∀ i1 i2 : Nat,
      xs.Nodup →
      antisymmetric_over_list leT xs →
      List.IsChain (fun a b => leT a b = true) xs →
      leT (xs.getD i1 default) (xs.getD i2 default) = true →
      i1 < xs.length →
      i2 < xs.length →
      i1 ≤ i2 := by
  intro i1 i2 UNIQ ANTI SORT REL SIZE1 SIZE2
  by_contra hlt
  have hlt : i2 < i1 := by omega
  have REL' := sorted_lt_idx_implies_rel T leT xs default H_leT_is_transitive i2 i1 SORT hlt SIZE1
  rw [getD_lt SIZE1, getD_lt SIZE2] at REL
  rw [getD_lt SIZE2, getD_lt SIZE1] at REL'
  have EQ := ANTI _ _ (List.getElem_mem SIZE1) (List.getElem_mem SIZE2) REL REL'
  have := (List.Nodup.getElem_inj_iff UNIQ).mp EQ
  omega

theorem prev_le_next {T : Type u} (F : T → Nat) (xs : List T) («def» : T) (i k : Nat) :
    (∀ i, i < xs.length - 1 → F (xs.getD i «def») ≤ F (xs.getD (i + 1) «def»)) →
    i + k ≤ xs.length - 1 →
    F (xs.getD i «def») ≤ F (xs.getD (i + k) «def») := by
  intro ALL SIZE
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := ih (by omega)
      have h2 := ALL (i + k) (by omega)
      rw [show i + (k + 1) = i + k + 1 by omega]
      exact Nat.le_trans h1 h2

end Prosa.Classic.Util.Sorting
