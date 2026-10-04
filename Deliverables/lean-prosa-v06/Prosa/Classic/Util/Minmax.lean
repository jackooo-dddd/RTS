-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/minmax.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 19)

import Prosa.Util.Minmax
import Prosa.Classic.Util.Tactics
import Prosa.Classic.Util.Notation
import Prosa.Classic.Util.Sorting
import Prosa.Classic.Util.Nat
import Prosa.Classic.Util.List
import Mathlib.Data.List.FinRange

/-!
Minima and maxima of sequences (arg-min/arg-max with respect to a Boolean relation).

Representation notes:
* `seq T` is `List T`, `option T` is `Option T`; `Context {T1 T2 : eqType}` gives carriers
  with `[DecidableEq _]`; a relation `rel T` is `T → T → Bool`.
* `x \in l` in proposition position is `x ∈ l`; a Boolean equation
  `(x \in l) = (a <= x < b)` is `decide (x ∈ l) = (decide (a ≤ x) && decide (x < b))`;
  `s != None` in proposition position is `(!decide (s = none)) = true`; Boolean
  statements in proposition position are `… = true`.
* MathComp's `transitive R` is unfolded with its binder order
  (`∀ y x z, R x y = true → R y z = true → R x z = true`).
* `leq` as a relation is `fun x y => decide (x ≤ y)`; `id` is the identity function.
* `values_between a b` filters `map nat_of_ord (enum 'I_b)`, i.e.
  `(List.finRange b).map Fin.val`.
* `rem x s` (remove the first occurrence) is `List.erase s x`.
* The source re-exports the official v0.6 `util/minmax.v`, mirrored by the `export` of
  the accepted `Prosa.Util.Minmax` below.
-/

namespace Prosa.Classic.Util.Minmax

export Prosa.Util.Minmax (leq_bigmax_cond_seq leq_bigmax_sup bigmax_leq_seqP leq_big_max
  bigmax_ord_ltn_identity bigmax_ltn_ord bigmax_pred bigmax_witness bigmax_witness_diff
  bigmax_subset)

universe u v

/-! ### Arg-min and arg-max -/

def seq_argmin {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) : List T1 → Option T1
  | [] => none
  | x :: l' =>
      match seq_argmin rel F l' with
      | some y => if rel (F x) (F y) then some x else some y
      | none => some x

def seq_argmax {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) : List T1 → Option T1
  | [] => none
  | x :: l' =>
      match seq_argmax rel F l' with
      | some y => if rel (F y) (F x) then some x else some y
      | none => some x

theorem seq_argmin_exists {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) (x : T1) :
    x ∈ l → (!decide (seq_argmin rel F l = none)) = true := by
  intro IN
  cases l with
  | nil => simp at IN
  | cons a l' =>
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      unfold seq_argmin
      split <;> (try split) <;> simp

theorem seq_argmin_in_seq {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) (x : T1) :
    seq_argmin rel F l = some x → x ∈ l := by
  induction l generalizing x with
  | nil => intro h; simp [seq_argmin] at h
  | cons a l' ih =>
      intro ARG
      unfold seq_argmin at ARG
      cases h : seq_argmin rel F l' with
      | none =>
          rw [h] at ARG; dsimp only at ARG
          cases ARG; exact List.mem_cons_self
      | some s =>
          rw [h] at ARG; dsimp only at ARG
          by_cases hr : rel (F a) (F s) = true
          · rw [if_pos hr] at ARG; cases ARG; exact List.mem_cons_self
          · rw [if_neg hr] at ARG; cases ARG; exact List.mem_cons_of_mem _ (ih _ h)

theorem seq_argmax_exists {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) (x : T1) :
    x ∈ l → (!decide (seq_argmax rel F l = none)) = true := by
  intro IN
  cases l with
  | nil => simp at IN
  | cons a l' =>
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      unfold seq_argmax
      split <;> (try split) <;> simp

theorem seq_argmax_in_seq {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) (x : T1) :
    seq_argmax rel F l = some x → x ∈ l := by
  induction l generalizing x with
  | nil => intro h; simp [seq_argmax] at h
  | cons a l' ih =>
      intro ARG
      unfold seq_argmax at ARG
      cases h : seq_argmax rel F l' with
      | none =>
          rw [h] at ARG; dsimp only at ARG
          cases ARG; exact List.mem_cons_self
      | some s =>
          rw [h] at ARG; dsimp only at ARG
          by_cases hr : rel (F s) (F a) = true
          · rw [if_pos hr] at ARG; cases ARG; exact List.mem_cons_self
          · rw [if_neg hr] at ARG; cases ARG; exact List.mem_cons_of_mem _ (ih _ h)

/-- LEAN_HELPER: `seq_argmin` of a list with an element is not `none`. -/
private theorem seq_argmin_ne_none {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) (x : T1) (IN : x ∈ l) :
    seq_argmin rel F l ≠ none := by
  have := seq_argmin_exists rel F l x IN
  simpa using this

/-- LEAN_HELPER: `seq_argmax` of a list with an element is not `none`. -/
private theorem seq_argmax_ne_none {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) (x : T1) (IN : x ∈ l) :
    seq_argmax rel F l ≠ none := by
  have := seq_argmax_exists rel F l x IN
  simpa using this

theorem seq_argmin_computes_min {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2)
    (H_transitive : ∀ y x z, rel x y = true → rel y z = true → rel x z = true) :
    ∀ l : List T1,
      (∀ x y, x ∈ l → y ∈ l → (rel (F x) (F y) || rel (F y) (F x)) = true) →
      ∀ x y, seq_argmin rel F l = some x → y ∈ l → rel (F x) (F y) = true := by
  intro l
  induction l with
  | nil => intro _ x y _ IN; simp at IN
  | cons a l' ih =>
      intro TOT x y EQmin IN
      have TOT' : ∀ x y, x ∈ l' → y ∈ l' → (rel (F x) (F y) || rel (F y) (F x)) = true :=
        fun x y hx hy => TOT x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)
      have REFL : ∀ z, z ∈ a :: l' → rel (F z) (F z) = true := by
        intro z hz
        have := TOT z z hz hz
        simpa using this
      unfold seq_argmin at EQmin
      cases ARG : seq_argmin rel F l' with
      | none =>
          rw [ARG] at EQmin; dsimp only at EQmin
          cases EQmin
          rcases List.mem_cons.mp IN with rfl | IN'
          · exact REFL _ List.mem_cons_self
          · exact absurd ARG (seq_argmin_ne_none rel F l' y IN')
      | some s =>
          rw [ARG] at EQmin; dsimp only at EQmin
          have Hs : s ∈ l' := seq_argmin_in_seq rel F l' s ARG
          by_cases REL : rel (F a) (F s) = true
          · rw [if_pos REL] at EQmin
            cases EQmin
            rcases List.mem_cons.mp IN with rfl | IN'
            · exact REFL _ List.mem_cons_self
            · exact H_transitive _ _ _ REL (ih TOT' s y ARG IN')
          · rw [if_neg REL] at EQmin
            cases EQmin
            rcases List.mem_cons.mp IN with rfl | IN'
            · have := TOT y x List.mem_cons_self (List.mem_cons_of_mem _ Hs)
              simp only [Bool.or_eq_true] at this
              rcases this with h | h
              · exact absurd h REL
              · exact h
            · exact ih TOT' x y ARG IN'

theorem seq_argmax_computes_max {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2)
    (H_transitive : ∀ y x z, rel x y = true → rel y z = true → rel x z = true) :
    ∀ l : List T1,
      (∀ x y, x ∈ l → y ∈ l → (rel (F x) (F y) || rel (F y) (F x)) = true) →
      ∀ x y, seq_argmax rel F l = some x → y ∈ l → rel (F y) (F x) = true := by
  intro l
  induction l with
  | nil => intro _ x y _ IN; simp at IN
  | cons a l' ih =>
      intro TOT x y EQmax IN
      have TOT' : ∀ x y, x ∈ l' → y ∈ l' → (rel (F x) (F y) || rel (F y) (F x)) = true :=
        fun x y hx hy => TOT x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)
      have REFL : ∀ z, z ∈ a :: l' → rel (F z) (F z) = true := by
        intro z hz
        have := TOT z z hz hz
        simpa using this
      unfold seq_argmax at EQmax
      cases ARG : seq_argmax rel F l' with
      | none =>
          rw [ARG] at EQmax; dsimp only at EQmax
          cases EQmax
          rcases List.mem_cons.mp IN with rfl | IN'
          · exact REFL _ List.mem_cons_self
          · exact absurd ARG (seq_argmax_ne_none rel F l' y IN')
      | some s =>
          rw [ARG] at EQmax; dsimp only at EQmax
          have Hs : s ∈ l' := seq_argmax_in_seq rel F l' s ARG
          by_cases REL : rel (F s) (F a) = true
          · rw [if_pos REL] at EQmax
            cases EQmax
            rcases List.mem_cons.mp IN with rfl | IN'
            · exact REFL _ List.mem_cons_self
            · exact H_transitive _ _ _ (ih TOT' s y ARG IN') REL
          · rw [if_neg REL] at EQmax
            cases EQmax
            rcases List.mem_cons.mp IN with rfl | IN'
            · have := TOT y x List.mem_cons_self (List.mem_cons_of_mem _ Hs)
              simp only [Bool.or_eq_true] at this
              rcases this with h | h
              · exact h
              · exact absurd h REL
            · exact ih TOT' x y ARG IN'

/-! ### Minimum and maximum with respect to a relation -/

def seq_min {T : Type u} [DecidableEq T] (rel : T → T → Bool) : List T → Option T :=
  seq_argmin rel id

def seq_max {T : Type u} [DecidableEq T] (rel : T → T → Bool) : List T → Option T :=
  seq_argmax rel id

theorem seq_min_exists {T : Type u} [DecidableEq T] (rel : T → T → Bool) (l : List T) (x : T) :
    x ∈ l → (!decide (seq_min rel l = none)) = true :=
  seq_argmin_exists rel id l x

theorem seq_min_in_seq {T : Type u} [DecidableEq T] (rel : T → T → Bool) (l : List T) (x : T) :
    seq_min rel l = some x → x ∈ l :=
  seq_argmin_in_seq rel id l x

theorem seq_max_exists {T : Type u} [DecidableEq T] (rel : T → T → Bool) (l : List T) (x : T) :
    x ∈ l → (!decide (seq_max rel l = none)) = true :=
  seq_argmax_exists rel id l x

theorem seq_max_in_seq {T : Type u} [DecidableEq T] (rel : T → T → Bool) (l : List T) (x : T) :
    seq_max rel l = some x → x ∈ l :=
  seq_argmax_in_seq rel id l x

theorem seq_min_computes_min {T : Type u} [DecidableEq T] (rel : T → T → Bool)
    (H_transitive : ∀ y x z, rel x y = true → rel y z = true → rel x z = true) :
    ∀ l : List T,
      (∀ x y, x ∈ l → y ∈ l → (rel x y || rel y x) = true) →
      ∀ x y, seq_min rel l = some x → y ∈ l → rel x y = true :=
  seq_argmin_computes_min rel id H_transitive

theorem seq_max_computes_max {T : Type u} [DecidableEq T] (rel : T → T → Bool)
    (H_transitive : ∀ y x z, rel x y = true → rel y z = true → rel x z = true) :
    ∀ l : List T,
      (∀ x y, x ∈ l → y ∈ l → (rel x y || rel y x) = true) →
      ∀ x y, seq_max rel l = some x → y ∈ l → rel y x = true :=
  seq_argmax_computes_max rel id H_transitive

/-! ### Arg-min and arg-max of a natural-number function -/

def seq_argmin_nat {T : Type u} [DecidableEq T] (F : T → Nat) : List T → Option T :=
  seq_argmin (fun x y => decide (x ≤ y)) F

def seq_argmax_nat {T : Type u} [DecidableEq T] (F : T → Nat) : List T → Option T :=
  seq_argmax (fun x y => decide (x ≤ y)) F

theorem seq_argmin_nat_exists {T : Type u} [DecidableEq T] (F : T → Nat) (l : List T) (x : T) :
    x ∈ l → (!decide (seq_argmin_nat F l = none)) = true :=
  seq_argmin_exists _ F l x

theorem seq_argmin_nat_in_seq {T : Type u} [DecidableEq T] (F : T → Nat) (l : List T) (x : T) :
    seq_argmin_nat F l = some x → x ∈ l :=
  seq_argmin_in_seq _ F l x

theorem seq_argmax_nat_exists {T : Type u} [DecidableEq T] (F : T → Nat) (l : List T) (x : T) :
    x ∈ l → (!decide (seq_argmax_nat F l = none)) = true :=
  seq_argmax_exists _ F l x

theorem seq_argmax_nat_in_seq {T : Type u} [DecidableEq T] (F : T → Nat) (l : List T) (x : T) :
    seq_argmax_nat F l = some x → x ∈ l :=
  seq_argmax_in_seq _ F l x

/-- LEAN_HELPER: `leq` is transitive (MathComp binder order). -/
private theorem leq_trans' : ∀ y x z : Nat, decide (x ≤ y) = true → decide (y ≤ z) = true →
    decide (x ≤ z) = true := by
  intro y x z h1 h2
  simp only [decide_eq_true_eq] at *
  exact Nat.le_trans h1 h2

/-- LEAN_HELPER: `leq` is total. -/
private theorem leq_total' (a b : Nat) : (decide (a ≤ b) || decide (b ≤ a)) = true := by
  rcases Nat.le_total a b with h | h <;> simp [h]

theorem seq_argmin_nat_computes_min {T : Type u} [DecidableEq T] (F : T → Nat) (l : List T)
    (x y : T) :
    seq_argmin_nat F l = some x → y ∈ l → F x ≤ F y := by
  intro SOME IN
  have := seq_argmin_computes_min (fun a b => decide (a ≤ b)) F leq_trans' l
    (fun a b _ _ => leq_total' (F a) (F b)) x y SOME IN
  simpa using this

theorem seq_argmax_nat_computes_max {T : Type u} [DecidableEq T] (F : T → Nat) (l : List T)
    (x y : T) :
    seq_argmax_nat F l = some x → y ∈ l → F y ≤ F x := by
  intro SOME IN
  have := seq_argmax_computes_max (fun a b => decide (a ≤ b)) F leq_trans' l
    (fun a b _ _ => leq_total' (F a) (F b)) x y SOME IN
  simpa using this

/-! ### Minimum and maximum of natural numbers -/

def seq_min_nat : List Nat → Option Nat :=
  seq_argmin (fun x y => decide (x ≤ y)) id

def seq_max_nat : List Nat → Option Nat :=
  seq_argmax (fun x y => decide (x ≤ y)) id

theorem seq_min_nat_exists (l : List Nat) (x : Nat) :
    x ∈ l → (!decide (seq_min_nat l = none)) = true :=
  seq_argmin_exists _ id l x

theorem seq_min_nat_in_seq (l : List Nat) (x : Nat) :
    seq_min_nat l = some x → x ∈ l :=
  seq_argmin_in_seq _ id l x

theorem seq_max_nat_exists (l : List Nat) (x : Nat) :
    x ∈ l → (!decide (seq_max_nat l = none)) = true :=
  seq_argmax_exists _ id l x

theorem seq_max_nat_in_seq (l : List Nat) (x : Nat) :
    seq_max_nat l = some x → x ∈ l :=
  seq_argmax_in_seq _ id l x

theorem seq_min_nat_computes_min (l : List Nat) (x y : Nat) :
    seq_min_nat l = some x → y ∈ l → x ≤ y := by
  intro SOME IN
  have := seq_argmin_computes_min (fun a b => decide (a ≤ b)) id leq_trans' l
    (fun a b _ _ => leq_total' a b) x y SOME IN
  simpa using this

theorem seq_max_nat_computes_max (l : List Nat) (x y : Nat) :
    seq_max_nat l = some x → y ∈ l → y ≤ x := by
  intro SOME IN
  have := seq_argmax_computes_max (fun a b => decide (a ≤ b)) id leq_trans' l
    (fun a b _ _ => leq_total' a b) x y SOME IN
  simpa using this

/-! ### Natural-number ranges -/

def values_between (a b : Nat) : List Nat :=
  ((List.finRange b).map Fin.val).filter (fun x => decide (a ≤ x))

theorem mem_values_between (a b : Nat) (x : Nat) :
    decide (x ∈ values_between a b) = (decide (a ≤ x) && decide (x < b)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [values_between, decide_eq_true_eq, Bool.and_eq_true, List.mem_filter,
    List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact ⟨h, i.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨x, h2⟩, rfl⟩, h1⟩

def min_nat_cond (P : Nat → Bool) (a b : Nat) : Option Nat :=
  seq_min_nat ((values_between a b).filter P)

def max_nat_cond (P : Nat → Bool) (a b : Nat) : Option Nat :=
  seq_max_nat ((values_between a b).filter P)

/-- LEAN_HELPER: membership in the filtered range. -/
private theorem mem_filter_values_between (P : Nat → Bool) (a b x : Nat) :
    x ∈ (values_between a b).filter P ↔ P x = true ∧ a ≤ x ∧ x < b := by
  rw [List.mem_filter]
  have := mem_values_between a b x
  rw [Bool.eq_iff_iff] at this
  simp only [decide_eq_true_eq, Bool.and_eq_true] at this
  rw [this]
  tauto

theorem min_nat_cond_exists (P : Nat → Bool) (a b x : Nat) :
    (decide (a ≤ x) && decide (x < b)) = true → P x = true →
    (!decide (min_nat_cond P a b = none)) = true := by
  intro LE HOLDS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at LE
  exact seq_argmin_exists _ id _ x ((mem_filter_values_between P a b x).mpr ⟨HOLDS, LE⟩)

theorem min_nat_cond_in_seq (P : Nat → Bool) (a b : Nat) (x : Nat) :
    min_nat_cond P a b = some x → (decide (a ≤ x) && decide (x < b)) = true ∧ P x = true := by
  intro SOME
  have := (mem_filter_values_between P a b x).mp (seq_min_nat_in_seq _ x SOME)
  exact ⟨by simp [this.2.1, this.2.2], this.1⟩

theorem min_nat_cond_computes_min (P : Nat → Bool) (a b : Nat) (x : Nat) :
    min_nat_cond P a b = some x →
    ∀ y, (decide (a ≤ y) && decide (y < b)) = true → P y = true → x ≤ y := by
  intro SOME y LE Py
  simp only [Bool.and_eq_true, decide_eq_true_eq] at LE
  exact seq_min_nat_computes_min _ x y SOME ((mem_filter_values_between P a b y).mpr ⟨Py, LE⟩)

theorem max_nat_cond_exists (P : Nat → Bool) (a b x : Nat) :
    (decide (a ≤ x) && decide (x < b)) = true → P x = true →
    (!decide (max_nat_cond P a b = none)) = true := by
  intro LE HOLDS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at LE
  exact seq_argmax_exists _ id _ x ((mem_filter_values_between P a b x).mpr ⟨HOLDS, LE⟩)

theorem max_nat_cond_in_seq (P : Nat → Bool) (a b : Nat) (x : Nat) :
    max_nat_cond P a b = some x → (decide (a ≤ x) && decide (x < b)) = true ∧ P x = true := by
  intro SOME
  have := (mem_filter_values_between P a b x).mp (seq_max_nat_in_seq _ x SOME)
  exact ⟨by simp [this.2.1, this.2.2], this.1⟩

theorem max_nat_cond_computes_max (P : Nat → Bool) (a b : Nat) (x : Nat) :
    max_nat_cond P a b = some x →
    ∀ y, (decide (a ≤ y) && decide (y < b)) = true → P y = true → y ≤ x := by
  intro SOME y LE Py
  simp only [Bool.and_eq_true, decide_eq_true_eq] at LE
  exact seq_max_nat_computes_max _ x y SOME ((mem_filter_values_between P a b y).mpr ⟨Py, LE⟩)

/-! ### The k smallest elements -/

def seq_argmin_k {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (l : List T1) : Nat → List T1
  | 0 => []
  | k' + 1 =>
      match seq_argmin rel F l with
      | some min_x => min_x :: seq_argmin_k rel F (l.erase min_x) k'
      | none => []

theorem seq_argmin_k_exists {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2]
    (rel : T2 → T2 → Bool) (F : T1 → T2) (k : Nat) (l : List T1) (x : T1) :
    1 ≤ k → x ∈ l → (!decide (seq_argmin_k rel F l k = [])) = true := by
  intro POS IN
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' POS
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  unfold seq_argmin_k
  cases h : seq_argmin rel F l with
  | none => exact absurd h (seq_argmin_ne_none rel F l x IN)
  | some m => simp

end Prosa.Classic.Util.Minmax
