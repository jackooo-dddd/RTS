-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/pick.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 2)

import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find

/-!
Picking numbers in an interval `[0, n)`.

Representation notes:
* `'I_n` is `Fin n`; a predicate `pred T` (and MathComp's `simpl_pred T`) is a
  Boolean function `T → Bool`.
* MathComp's `pick P` on `'I_n` is the first ordinal of `enum 'I_n` (increasing
  order) that satisfies `P`, i.e. `(List.finRange n).find? P`.
* `[pred i | P i & [forall j : 'I_n, P j ==> ord i j]]` is
  `fun i => P i && (List.finRange n).all (fun j => !P j || ord i j)`; the
  relation of `arg_pred_nat` is on ordinals, and `leq`/`geq` used there compare
  the ordinals through `nat_of_ord` (`i.val`).
* The `[pick-… x … N | P]` notations are parsing-only and have no Lean counterpart.
* Boolean predicates in proposition position are `p x = true`; `x < n` is the Nat order.
-/

namespace Prosa.Classic.Util.Pick

def default0 {n : Nat} (x : Option (Fin n)) : Nat :=
  match x with
  | some y => y.val
  | none => 0

def arg_pred_nat (n : Nat) (P : Fin n → Bool) (ord : Fin n → Fin n → Bool) : Fin n → Bool :=
  fun i => P i && (List.finRange n).all (fun j => !P j || ord i j)

def pred_min_nat (n : Nat) (P : Fin n → Bool) : Fin n → Bool :=
  arg_pred_nat n P (fun x y => decide (x.val ≤ y.val))

def pred_max_nat (n : Nat) (P : Fin n → Bool) : Fin n → Bool :=
  arg_pred_nat n P (fun x y => decide (y.val ≤ x.val))

def to_pred_ord (n : Nat) (P : Nat → Bool) : Fin n → Bool :=
  fun x => P x.val

def pick_any (n : Nat) (P : Nat → Bool) : Nat :=
  default0 ((List.finRange n).find? (to_pred_ord n P))

def pick_min (n : Nat) (P : Nat → Bool) : Nat :=
  default0 ((List.finRange n).find? (pred_min_nat n (to_pred_ord n P)))

def pick_max (n : Nat) (P : Nat → Bool) : Nat :=
  default0 ((List.finRange n).find? (pred_max_nat n (to_pred_ord n P)))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: `find?` over all ordinals succeeds as soon as one ordinal satisfies the predicate. -/
private theorem find?_finRange_some {n : Nat} (q : Fin n → Bool) (i : Fin n) (hi : q i = true) :
    ∃ y, (List.finRange n).find? q = some y ∧ q y = true := by
  cases h : (List.finRange n).find? q with
  | none =>
      rw [List.find?_eq_none] at h
      exact absurd hi (h i (List.mem_finRange i))
  | some y => exact ⟨y, rfl, List.find?_some h⟩

/-- LEAN_HELPER: membership in `pred_min_nat`/`pred_max_nat` unfolds to a quantified statement. -/
private theorem arg_pred_nat_iff {n : Nat} (P : Fin n → Bool) (ord : Fin n → Fin n → Bool)
    (i : Fin n) :
    arg_pred_nat n P ord i = true ↔ P i = true ∧ ∀ j : Fin n, P j = true → ord i j = true := by
  unfold arg_pred_nat
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    rcases h2 j with h | h
    · rw [hj] at h; exact absurd h (by decide)
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    cases hj : P j
    · exact Or.inl rfl
    · exact Or.inr (h2 j hj)

/-! ### Lemmas about pick_any -/

theorem pick_any_holds (n : Nat) (p : Nat → Bool) (P : Nat → Prop)
    (EX : ∃ x, x < n ∧ p x = true) (HOLDS : ∀ x, p x = true → P x) :
    P (pick_any n p) := by
  obtain ⟨x, LT, PRED⟩ := EX
  obtain ⟨y, hy, hq⟩ := find?_finRange_some (to_pred_ord n p) ⟨x, LT⟩ PRED
  unfold pick_any
  rw [hy]
  exact HOLDS y.val hq

/-! ### Lemmas about pick_min -/

/-- LEAN_HELPER: the minimum computed by `pick_min` (shared by `pick_min_ltn` and `pick_min_holds`). -/
private theorem pick_min_spec (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    ∃ y : Fin n, pick_min n p = y.val ∧ p y.val = true ∧
      ∀ z, z < n → p z = true → y.val ≤ z := by
  classical
  have hex : ∃ x, x < n ∧ p x = true := EX
  let m := Nat.find hex
  have hm : m < n ∧ p m = true := Nat.find_spec hex
  have hmin : ∀ z, z < n → p z = true → m ≤ z := fun z hz hp => Nat.find_min' hex ⟨hz, hp⟩
  have hq : pred_min_nat n (to_pred_ord n p) ⟨m, hm.1⟩ = true := by
    unfold pred_min_nat
    rw [arg_pred_nat_iff]
    refine ⟨hm.2, fun j hj => ?_⟩
    simpa using hmin j.val j.isLt hj
  obtain ⟨y, hy, hqy⟩ := find?_finRange_some _ _ hq
  unfold pred_min_nat at hqy
  rw [arg_pred_nat_iff] at hqy
  refine ⟨y, by unfold pick_min; rw [hy]; rfl, hqy.1, fun z hz hp => ?_⟩
  have := hqy.2 ⟨z, hz⟩ hp
  simpa using this

theorem pick_min_ltn (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    pick_min n p < n := by
  obtain ⟨y, hy, _, _⟩ := pick_min_spec n p EX
  rw [hy]
  exact y.isLt

theorem pick_min_holds (n : Nat) (p : Nat → Bool) (P : Nat → Prop)
    (EX : ∃ x, x < n ∧ p x = true)
    (MIN : ∀ x, x < n → p x = true → (∀ y, y < n → p y = true → x ≤ y) → P x) :
    P (pick_min n p) := by
  obtain ⟨y, hy, hp, hmin⟩ := pick_min_spec n p EX
  rw [hy]
  exact MIN y.val y.isLt hp hmin

/-! ### Lemmas about pick_max -/

/-- LEAN_HELPER: the maximum computed by `pick_max`. -/
private theorem pick_max_spec (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    ∃ y : Fin n, pick_max n p = y.val ∧ p y.val = true ∧
      ∀ z, z < n → p z = true → z ≤ y.val := by
  classical
  obtain ⟨x, hxn, hxp⟩ := EX
  let Q : Nat → Prop := fun z => z < n ∧ p z = true
  let m := Nat.findGreatest Q n
  have hm : Q m := Nat.findGreatest_spec (P := Q) (Nat.le_of_lt hxn) ⟨hxn, hxp⟩
  have hmax : ∀ z, z < n → p z = true → z ≤ m := fun z hz hp =>
    Nat.le_findGreatest (P := Q) (Nat.le_of_lt hz) ⟨hz, hp⟩
  have hq : pred_max_nat n (to_pred_ord n p) ⟨m, hm.1⟩ = true := by
    unfold pred_max_nat
    rw [arg_pred_nat_iff]
    refine ⟨hm.2, fun j hj => ?_⟩
    simpa using hmax j.val j.isLt hj
  obtain ⟨y, hy, hqy⟩ := find?_finRange_some _ _ hq
  unfold pred_max_nat at hqy
  rw [arg_pred_nat_iff] at hqy
  refine ⟨y, by unfold pick_max; rw [hy]; rfl, hqy.1, fun z hz hp => ?_⟩
  have := hqy.2 ⟨z, hz⟩ hp
  simpa using this

theorem pick_max_ltn (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    pick_max n p < n := by
  obtain ⟨y, hy, _, _⟩ := pick_max_spec n p EX
  rw [hy]
  exact y.isLt

theorem pick_max_holds (n : Nat) (p : Nat → Bool) (P : Nat → Prop)
    (EX : ∃ x, x < n ∧ p x = true)
    (MAX : ∀ x, x < n → p x = true → (∀ y, y < n → p y = true → y ≤ x) → P x) :
    P (pick_max n p) := by
  obtain ⟨y, hy, hp, hmax⟩ := pick_max_spec n p EX
  rw [hy]
  exact MAX y.val y.isLt hp hmax

/-! ### The picked number satisfies the predicate -/

theorem pick_any_pred (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    p (pick_any n p) = true :=
  pick_any_holds n p (fun x => p x = true) EX (fun _ h => h)

theorem pick_min_pred (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    p (pick_min n p) = true :=
  pick_min_holds n p (fun x => p x = true) EX (fun _ _ h _ => h)

theorem pick_max_pred (n : Nat) (p : Nat → Bool) (EX : ∃ x, x < n ∧ p x = true) :
    p (pick_max n p) = true :=
  pick_max_holds n p (fun x => p x = true) EX (fun _ _ h _ => h)

/-! ### Comparing minima -/

theorem pick_min_compare (n : Nat) (p1 p2 : Nat → Bool)
    (EX1 : ∃ x, x < n ∧ p1 x = true) (EX2 : ∃ x, x < n ∧ p2 x = true)
    (OUT : ∀ x y, x < n → y < n → p1 x = true → p2 y = true → (!p1 y) = true → x ≤ y) :
    pick_min n p1 ≤ pick_min n p2 := by
  cases IN : p1 (pick_min n p2)
  · exact OUT _ _ (pick_min_ltn n p1 EX1) (pick_min_ltn n p2 EX2) (pick_min_pred n p1 EX1)
      (pick_min_pred n p2 EX2) (by rw [IN]; rfl)
  · exact pick_min_holds n p1 (fun x => x ≤ pick_min n p2) EX1
      (fun x _ _ ALL => ALL _ (pick_min_ltn n p2 EX2) IN)

end Prosa.Classic.Util.Pick
