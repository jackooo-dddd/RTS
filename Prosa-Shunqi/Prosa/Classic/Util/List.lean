-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/list.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 9)

import Prosa.Util.List
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

/-!
Lemmas about lists.  The source re-exports `prosa.util.list` (imported above).

Representation notes (following the accepted v0.6 conventions):
* `seq T` is `List T`; `size` is `length`; `uniq` is `Nodup`; `index x l` is
  `l.idxOf x`; `nth x0 l i` is `l.getD i x0`; `rcons s x` is `s ++ [x]`;
  `take`, `filter`, `map`, `zip` are the Lean list functions; `nseq` is
  `List.replicate`; `pmap` is `List.filterMap`; `unzip1`/`unzip2` are
  `List.map Prod.fst`/`List.map Prod.snd`.
* `Context {T : eqType}` is a carrier with `[DecidableEq T]`.
* `is_true (x \in l)` is `x ∈ l` and `x \notin l` is `x ∉ l`; a Boolean equation
  `(x \in a) = (x \in b)` is `decide (x ∈ a) = decide (x ∈ b)`; `~~ b` in
  proposition position is `(!b) = true`.
* `reflect P b` is the informative `BoolReflect P b` (as in the accepted v0.6
  files), defined below as a Lean helper.
* The section-local `Let max := foldl maxn 0` is unfolded in `seq_max_cons`,
  exactly as Rocq abstracts it when the section is closed.
* `set_nth_if_exists` uses `List.set`, which agrees with MathComp's
  `set_nth x0 l n y` whenever `n < size l` (the only case the source uses);
  the default element of the `Program` obligation is therefore irrelevant.
* `set_pair_1nd` is translated faithfully: like the source, it replaces the
  second component.
-/

namespace Prosa.Classic.Util.List

universe u v

/-- LEAN_HELPER: informative Boolean reflection, the Lean form of `reflect`. -/
inductive BoolReflect (P : Prop) : Bool → Type where
  | isTrue : P → BoolReflect P true
  | isFalse : ¬ P → BoolReflect P false

/-- LEAN_HELPER: build a reflection view from an equivalence. -/
def BoolReflect.ofIff {P : Prop} {b : Bool} (h : P ↔ b = true) : BoolReflect P b :=
  match b, h with
  | true, h => BoolReflect.isTrue (h.mpr rfl)
  | false, h => BoolReflect.isFalse (fun p => Bool.false_ne_true (h.mp p))

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt {α : Type u} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- LEAN_HELPER: defaulted lookup outside the list. -/
private theorem getD_ge {α : Type u} {l : List α} {i : Nat} {d : α} (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ### Lists without duplicates -/

/-- LEAN_HELPER: on a duplicate-free list, keeping the elements whose index is
below `k` is taking the first `k` elements. -/
private theorem filter_idxOf_lt_eq_take {T : Type u} [DecidableEq T] :
    ∀ (l : List T), l.Nodup → ∀ k,
      l.filter (fun x => decide (l.idxOf x < k)) = l.take k := by
  intro l
  induction l with
  | nil => intro _ k; simp
  | cons a t ih =>
      intro hnd k
      rw [List.nodup_cons] at hnd
      obtain ⟨hnot, hnd⟩ := hnd
      cases k with
      | zero =>
          simp only [List.take_zero, List.filter_eq_nil_iff, decide_eq_true_eq]
          intro x _; omega
      | succ k =>
          rw [List.filter_cons]
          simp only [List.idxOf_cons, beq_self_eq_true, cond_true, Nat.zero_lt_succ,
            decide_true, ↓reduceIte, List.take_succ_cons]
          congr 1
          have hc : ∀ x ∈ t,
              decide ((bif a == x then 0 else t.idxOf x + 1) < k + 1) =
                decide (t.idxOf x < k) := by
            intro x hx
            have hne : (a == x) = false := by
              simp only [beq_eq_false_iff_ne]
              intro h; subst h; exact hnot hx
            simp [hne]
          rw [List.filter_congr hc, ih hnd k]

theorem idx_lt_rcons {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (i : Nat) (x0 : T),
      l.Nodup →
      i < l.length →
      l.filter (fun x => decide (l.idxOf x < i + 1)) =
        l.filter (fun x => decide (l.idxOf x < i)) ++ [l.getD i x0] := by
  intro l i x0 UNIQ LT
  rw [filter_idxOf_lt_eq_take l UNIQ, filter_idxOf_lt_eq_take l UNIQ,
    List.take_succ, List.getElem?_eq_getElem LT, getD_lt LT]
  rfl

theorem filter_idx_lt_take {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (i : Nat),
      l.Nodup →
      i < l.length →
      l.filter (fun x => decide (l.idxOf x < i)) = l.take i := by
  intro l i UNIQ _
  exact filter_idxOf_lt_eq_take l UNIQ i

theorem filter_idx_le_takeS {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (i : Nat),
      l.Nodup →
      i < l.length →
      l.filter (fun x => decide (l.idxOf x ≤ i)) = l.take (i + 1) := by
  intro l i UNIQ _
  rw [← filter_idxOf_lt_eq_take l UNIQ (i + 1)]
  congr 1
  funext x
  simp only [decide_eq_decide]
  omega

def mapP2 (T : Type u) {T' : Type v} [DecidableEq T'] (s : List T) (f : T → T') (y : T') :
    BoolReflect (∃ x, x ∈ s ∧ y = f x) (decide (y ∈ s.map f)) :=
  BoolReflect.ofIff (by
    simp only [List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩)

/-! ### Zip -/

def zipP {T : Type u} [DecidableEq T] (x0 : T) (P : T → T → Bool) (X Y : List T)
    (SIZE : X.length = Y.length) :
    BoolReflect (∀ i, i < (X.zip Y).length → P (X.getD i x0) (Y.getD i x0) = true)
      ((X.zip Y).all (fun p => P p.1 p.2)) :=
  BoolReflect.ofIff (by
    rw [List.all_eq_true]
    constructor
    · intro H p hp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      have hiX : i < X.length := by simp at hi; omega
      have hiY : i < Y.length := by simp at hi; omega
      have := H i hi
      rw [getD_lt hiX, getD_lt hiY] at this
      simpa [List.getElem_zip] using this
    · intro H i hi
      have hiX : i < X.length := by simp at hi; omega
      have hiY : i < Y.length := by simp at hi; omega
      have := H _ (List.getElem_mem hi)
      rw [getD_lt hiX, getD_lt hiY]
      simpa [List.getElem_zip] using this)

theorem mem_zip_exists :
    ∀ (T : Type u) (T' : Type v) [DecidableEq T] [DecidableEq T']
      (x1 : T) (x2 : T') (l1 : List T) (l2 : List T') (elem : T) (elem' : T'),
      l1.length = l2.length →
      (x1, x2) ∈ l1.zip l2 →
      ∃ idx,
        idx < l1.length ∧
        idx < l2.length ∧
        x1 = l1.getD idx elem ∧
        x2 = l2.getD idx elem' := by
  intro T T' _ _ x1 x2 l1 l2 elem elem' _ IN
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem IN
  have hi1 : i < l1.length := by simp at hi; omega
  have hi2 : i < l2.length := by simp at hi; omega
  rw [List.getElem_zip] at hget
  simp only [Prod.mk.injEq] at hget
  refine ⟨i, hi1, hi2, ?_, ?_⟩
  · rw [getD_lt hi1]; exact hget.1.symm
  · rw [getD_lt hi2]; exact hget.2.symm

theorem mem_zip :
    ∀ (T : Type u) (T' : Type v) [DecidableEq T] [DecidableEq T']
      (x1 : T) (x2 : T') (l1 : List T) (l2 : List T'),
      l1.length = l2.length →
      (x1, x2) ∈ l1.zip l2 →
      x1 ∈ l1 ∧ x2 ∈ l2 := by
  intro T T' _ _ x1 x2 l1 l2 _ IN
  exact List.of_mem_zip IN

theorem mem_zip_nseq_r {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2] :
    ∀ (x : T1) (y : T2) (n : Nat) (l : List T1),
      l.length = n →
      decide ((x, y) ∈ l.zip (List.replicate n y)) = decide (x ∈ l) := by
  intro x y n l SIZE
  subst SIZE
  apply decide_eq_decide.mpr
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        List.mem_cons, Prod.mk.injEq, and_true, ih]

theorem mem_zip_nseq_l {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2] :
    ∀ (x : T1) (y : T2) (n : Nat) (l : List T2),
      l.length = n →
      decide ((x, y) ∈ (List.replicate n x).zip l) = decide (y ∈ l) := by
  intro x y n l SIZE
  subst SIZE
  apply decide_eq_decide.mpr
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        List.mem_cons, Prod.mk.injEq, true_and, ih]

theorem unzip1_pair {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2] :
    ∀ (l : List T1) (f : T1 → T2),
      List.map Prod.fst (l.map fun x => (x, f x)) = l := by
  intro l f
  simp [Function.comp_def]

theorem unzip2_pair {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2] :
    ∀ (l : List T1) (f : T1 → T2),
      List.map Prod.snd (l.map fun x => (f x, x)) = l := by
  intro l f
  simp [Function.comp_def]

theorem eq_unzip1 {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2] :
    ∀ (l1 l2 : List (T1 × T2)) (x0 : T1 × T2),
      l1.length = l2.length →
      (∀ i, i < l1.length → (l1.getD i x0).1 = (l2.getD i x0).1) →
      List.map Prod.fst l1 = List.map Prod.fst l2 := by
  intro l1 l2 x0 SIZE ALL
  apply List.ext_getElem (by simpa using SIZE)
  intro i h1 h2
  have hi1 : i < l1.length := by simpa using h1
  have hi2 : i < l2.length := by simpa using h2
  have := ALL i hi1
  rw [getD_lt hi1, getD_lt hi2] at this
  simpa using this

theorem eq_unzip2 {T1 : Type u} {T2 : Type v} [DecidableEq T1] [DecidableEq T2] :
    ∀ (l1 l2 : List (T1 × T2)) (x0 : T1 × T2),
      l1.length = l2.length →
      (∀ i, i < l1.length → (l1.getD i x0).2 = (l2.getD i x0).2) →
      List.map Prod.snd l1 = List.map Prod.snd l2 := by
  intro l1 l2 x0 SIZE ALL
  apply List.ext_getElem (by simpa using SIZE)
  intro i h1 h2
  have hi1 : i < l1.length := by simpa using h1
  have hi2 : i < l2.length := by simpa using h2
  have := ALL i hi1
  rw [getD_lt hi1, getD_lt hi2] at this
  simpa using this

/-- Restatement of Rocq's `nth_error`. -/
def nth_or_none {T : Type u} : List T → Nat → Option T
  | x :: _, 0 => some x
  | _ :: l, n + 1 => nth_or_none l n
  | [], _ => none

/-! ### `nth` -/

theorem nth_in_or_default {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (x0 : T) (i : Nat),
      l.getD i x0 ∈ l ∨ l.getD i x0 = x0 := by
  intro l x0 i
  by_cases h : i < l.length
  · left; rw [getD_lt h]; exact List.getElem_mem h
  · right; rw [getD_ge (by omega)]

theorem nth_neq_default {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (x0 : T) (i : Nat) (y : T),
      l.getD i x0 = y →
      y ≠ x0 →
      y ∈ l := by
  intro l x0 i y NTH NEQ
  rcases nth_in_or_default l x0 i with IN | DEF
  · rwa [NTH] at IN
  · exact absurd (NTH ▸ DEF) NEQ

theorem nth_or_none_mem {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (n : Nat) (x : T), nth_or_none l n = some x → x ∈ l := by
  intro l
  induction l with
  | nil => intro n x h; cases n <;> simp [nth_or_none] at h
  | cons a l ih =>
      intro n x h
      cases n with
      | zero => simp only [nth_or_none, Option.some.injEq] at h; subst h; simp
      | succ n => exact List.mem_cons_of_mem a (ih n x h)

theorem nth_or_none_mem_exists {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (x : T), x ∈ l → ∃ n, nth_or_none l n = some x := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons a l ih =>
      intro x h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, rfl⟩
      · obtain ⟨n, hn⟩ := ih x h
        exact ⟨n + 1, hn⟩

theorem nth_or_none_size_none {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (n : Nat),
      nth_or_none l n = none ↔ l.length ≤ n := by
  intro l
  induction l with
  | nil => intro n; cases n <;> simp [nth_or_none]
  | cons a l ih =>
      intro n
      cases n with
      | zero => simp [nth_or_none]
      | succ n => simp [nth_or_none, ih n]

theorem nth_or_none_size_some {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (n : Nat) (x : T),
      nth_or_none l n = some x → n < l.length := by
  intro l
  induction l with
  | nil => intro n x h; cases n <;> simp [nth_or_none] at h
  | cons a l ih =>
      intro n x h
      cases n with
      | zero => simp
      | succ n => have := ih n x h; simp; omega

theorem nth_or_none_uniq {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (i j : Nat) (x : T),
      l.Nodup →
      nth_or_none l i = some x →
      nth_or_none l j = some x →
      i = j := by
  intro l
  induction l with
  | nil => intro i j x _ h; cases i <;> simp [nth_or_none] at h
  | cons a l ih =>
      intro i j x UNIQ SOMEi SOMEj
      rw [List.nodup_cons] at UNIQ
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              simp only [nth_or_none, Option.some.injEq] at SOMEi
              subst SOMEi
              exact absurd (nth_or_none_mem l j a SOMEj) UNIQ.1
      | succ i =>
          cases j with
          | zero =>
              simp only [nth_or_none, Option.some.injEq] at SOMEj
              subst SOMEj
              exact absurd (nth_or_none_mem l i a SOMEi) UNIQ.1
          | succ j => exact congrArg (· + 1) (ih i j x UNIQ.2 SOMEi SOMEj)

theorem nth_or_none_nth {T : Type u} [DecidableEq T] :
    ∀ (l : List T) (n : Nat) (x x0 : T),
      nth_or_none l n = some x →
      l.getD n x0 = x := by
  intro l
  induction l with
  | nil => intro n x x0 h; cases n <;> simp [nth_or_none] at h
  | cons a l ih =>
      intro n x x0 h
      cases n with
      | zero => simp only [nth_or_none, Option.some.injEq] at h; simp [h]
      | succ n => simpa using ih n x x0 h

/-! ### Partial maps -/

theorem pmap_inj_in_uniq {T : Type u} {T' : Type v} [DecidableEq T] [DecidableEq T']
    (s : List T) (f : T → Option T') :
    (∀ x y, x ∈ s → y ∈ s → f x = f y → x = y) →
    s.Nodup →
    (s.filterMap f).Nodup := by
  intro INJ UNIQ
  induction s with
  | nil => simp
  | cons a s ih =>
      rw [List.nodup_cons] at UNIQ
      have ih' := ih (fun x y hx hy h =>
        INJ x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy) h) UNIQ.2
      rw [List.filterMap_cons]
      cases hfa : f a with
      | none => simpa using ih'
      | some b =>
          simp only
          rw [List.nodup_cons]
          refine ⟨?_, ih'⟩
          intro hb
          obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
          have := INJ a a' List.mem_cons_self (List.mem_cons_of_mem _ ha') (by rw [hfa, hfa'])
          subst this
          exact UNIQ.1 ha'

theorem pmap_inj_uniq {T : Type u} {T' : Type v} [DecidableEq T] [DecidableEq T']
    (s : List T) (f : T → Option T') :
    Function.Injective f →
    s.Nodup →
    (s.filterMap f).Nodup := by
  intro INJ UNIQ
  exact pmap_inj_in_uniq s f (fun x y _ _ h => INJ h) UNIQ

/-! ### Replacing elements -/

/-- A `set_nth` that does not grow the list. -/
def set_nth_if_exists {T : Type u} (l : List T) (n : Nat) (y : T) : List T :=
  if n < l.length then l.set n y else l

/-- Replace the first element satisfying `P` by its image under `f`. -/
def replace_first {T : Type u} (P : T → Bool) (f : T → T) : List T → List T
  | x0 :: l' => if P x0 then f x0 :: l' else x0 :: replace_first P f l'
  | [] => []

/-- Replace the first element satisfying `P` by a constant. -/
def replace_first_const {T : Type u} (P : T → Bool) (y : T) (l : List T) : List T :=
  replace_first P (fun _ => y) l

/-- As in the source, this replaces the second component. -/
def set_pair_1nd {T1 : Type u} {T2 : Type v} (y : T2) (p : T1 × T2) : T1 × T2 :=
  (p.1, y)

def set_pair_2nd {T1 : Type u} {T2 : Type v} (y : T2) (p : T1 × T2) : T1 × T2 :=
  (p.1, y)

theorem replace_first_size {T : Type u} [DecidableEq T] (P : T → Bool) (f : T → T)
    (l : List T) :
    (replace_first P f l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => unfold replace_first; split <;> simp [ih]

theorem replace_first_cases {T : Type u} [DecidableEq T] {P : T → Bool} {f : T → T}
    {l : List T} {x : T} :
    x ∈ replace_first P f l →
    x ∈ l ∨ (∃ y, x = f y ∧ P y = true ∧ y ∈ l) := by
  intro IN
  induction l with
  | nil => exact absurd IN (by simp [replace_first])
  | cons a l ih =>
      unfold replace_first at IN
      split at IN
      · rcases List.mem_cons.mp IN with rfl | IN
        · exact Or.inr ⟨a, rfl, by assumption, List.mem_cons_self⟩
        · exact Or.inl (List.mem_cons_of_mem a IN)
      · rcases List.mem_cons.mp IN with rfl | IN
        · exact Or.inl List.mem_cons_self
        · rcases ih IN with h | ⟨y, h1, h2, h3⟩
          · exact Or.inl (List.mem_cons_of_mem a h)
          · exact Or.inr ⟨y, h1, h2, List.mem_cons_of_mem a h3⟩

theorem replace_first_no_change {T : Type u} [DecidableEq T] {P : T → Bool} {f : T → T}
    {l : List T} {x : T} :
    x ∈ l →
    (!P x) = true →
    x ∈ replace_first P f l := by
  intro IN NOT
  induction l with
  | nil => exact absurd IN (by simp)
  | cons a l ih =>
      unfold replace_first
      split
      · rcases List.mem_cons.mp IN with rfl | IN
        · simp_all
        · exact List.mem_cons_of_mem _ IN
      · rcases List.mem_cons.mp IN with rfl | IN
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih IN)

theorem replace_first_idempotent {T : Type u} [DecidableEq T] {P : T → Bool} {f : T → T}
    {l : List T} {x : T} :
    x ∈ l →
    f x = x →
    x ∈ replace_first P f l := by
  intro IN IDEMP
  induction l with
  | nil => exact absurd IN (by simp)
  | cons a l ih =>
      unfold replace_first
      split
      · rcases List.mem_cons.mp IN with rfl | IN
        · rw [IDEMP]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ IN
      · rcases List.mem_cons.mp IN with rfl | IN
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih IN)

theorem replace_first_new {T : Type u} [DecidableEq T] :
    ∀ (P : T → Bool) (f : T → T) (l : List T) (x1 x2 : T),
      x1 ∉ l →
      x2 ∉ l →
      x1 ∈ replace_first P f l →
      x2 ∈ replace_first P f l →
      x1 = x2 := by
  intro P f l x1 x2 NOT1 NOT2 IN1 IN2
  induction l with
  | nil => simp [replace_first] at IN1
  | cons a l ih =>
      simp only [List.mem_cons, not_or] at NOT1 NOT2
      by_cases HOLDS : P a = true
      · simp only [replace_first, HOLDS, ↓reduceIte, List.mem_cons] at IN1 IN2
        rcases IN1 with h1 | IN1
        · rcases IN2 with h2 | IN2
          · rw [h1, h2]
          · exact absurd IN2 NOT2.2
        · exact absurd IN1 NOT1.2
      · simp only [replace_first, HOLDS, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
          at IN1 IN2
        rcases IN1 with h1 | IN1
        · exact absurd h1 NOT1.1
        · rcases IN2 with h2 | IN2
          · exact absurd h2 NOT2.1
          · exact ih NOT1.2 NOT2.2 IN1 IN2

theorem replace_first_previous {T : Type u} [DecidableEq T] (P : T → Bool) (f : T → T)
    {l : List T} {x : T} :
    x ∈ l →
    x ∈ replace_first P f l ∨ (P x = true ∧ f x ∈ replace_first P f l) := by
  intro IN
  induction l with
  | nil => exact absurd IN (by simp)
  | cons a l ih =>
      unfold replace_first
      split
      · rcases List.mem_cons.mp IN with rfl | IN
        · exact Or.inr ⟨by assumption, List.mem_cons_self⟩
        · exact Or.inl (List.mem_cons_of_mem _ IN)
      · rcases List.mem_cons.mp IN with rfl | IN
        · exact Or.inl List.mem_cons_self
        · rcases ih IN with h | ⟨h1, h2⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem replace_first_failed {T : Type u} [DecidableEq T] (P : T → Bool) (f : T → T)
    {l : List T} :
    (∀ x, x ∈ l → f x ∉ replace_first P f l) →
    (∀ x, x ∈ l → (!P x) = true) := by
  intro NOTIN
  induction l with
  | nil => intro x IN; exact absurd IN (by simp)
  | cons a l ih =>
      intro x IN
      by_cases HOLDS : P a = true
      · exfalso
        apply NOTIN a List.mem_cons_self
        unfold replace_first
        simp [HOLDS]
      · rcases List.mem_cons.mp IN with rfl | IN
        · simpa using HOLDS
        · apply ih _ x IN
          intro y INy hy
          apply NOTIN y (List.mem_cons_of_mem _ INy)
          unfold replace_first
          simp only [Bool.not_eq_true] at HOLDS
          simp [HOLDS, hy]

/-! ### Lists of pairs as functions -/

def pairs_to_function {T1 : Type u} [DecidableEq T1] {T2 : Type v} (y0 : T2)
    (l : List (T1 × T2)) : T1 → T2 :=
  fun x => (List.map Prod.snd l).getD ((List.map Prod.fst l).idxOf x) y0

theorem pairs_to_function_neq_default {T1 : Type u} {T2 : Type v} [DecidableEq T1]
    [DecidableEq T2] (y0 : T2) (l : List (T1 × T2)) (x : T1) (y : T2) :
    pairs_to_function y0 l x = y →
    y ≠ y0 →
    (x, y) ∈ l := by
  intro PAIR NEQ
  induction l with
  | nil => simp [pairs_to_function] at PAIR; exact absurd PAIR.symm NEQ
  | cons a l ih =>
      obtain ⟨a1, a2⟩ := a
      simp only [pairs_to_function, List.map_cons, List.idxOf_cons] at PAIR
      by_cases h : a1 = x
      · subst h
        simp at PAIR
        simp [PAIR]
      · have hb : (a1 == x) = false := by simpa using h
        rw [hb] at PAIR
        simp only [cond_false, List.getD_cons_succ] at PAIR
        exact List.mem_cons_of_mem _ (ih PAIR)

theorem pairs_to_function_mem {T1 : Type u} {T2 : Type v} [DecidableEq T1]
    [DecidableEq T2] (y0 : T2) (l : List (T1 × T2)) (x : T1) (y : T2) :
    (List.map Prod.fst l).Nodup →
    (x, y) ∈ l →
    pairs_to_function y0 l x = y := by
  intro UNIQ IN
  induction l with
  | nil => exact absurd IN (by simp)
  | cons a l ih =>
      obtain ⟨x', y'⟩ := a
      simp only [List.map_cons, List.nodup_cons] at UNIQ
      simp only [pairs_to_function, List.map_cons, List.idxOf_cons]
      rcases List.mem_cons.mp IN with h | IN
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · by_cases hx : x' = x
        · subst hx
          exact absurd (List.mem_map_of_mem (f := Prod.fst) IN) UNIQ.1
        · have hb : (x' == x) = false := by simpa using hx
          rw [hb]
          simpa [pairs_to_function, cond_false] using ih UNIQ.2 IN

/-! ### Orders over lists -/

def total_over_list {T : Type u} [DecidableEq T] (rel : T → T → Bool) (l : List T) : Prop :=
  ∀ x1 x2,
    x1 ∈ l →
    x2 ∈ l →
    (rel x1 x2 = true ∨ rel x2 x1 = true)

def antisymmetric_over_list {T : Type u} [DecidableEq T] (rel : T → T → Bool)
    (l : List T) : Prop :=
  ∀ x1 x2,
    x1 ∈ l →
    x2 ∈ l →
    rel x1 x2 = true →
    rel x2 x1 = true →
    x1 = x2

/-! ### Additional lemmas -/

theorem in_cat {X : Type u} [DecidableEq X] :
    ∀ (x : X) (xs : List X),
      x ∈ xs → ∃ xsl xsr, xs = xsl ++ [x] ++ xsr := by
  intro x xs SUB
  obtain ⟨s, t, h⟩ := List.append_of_mem SUB
  exact ⟨s, t, by simp [h]⟩

theorem seq_max_cons :
    ∀ (x : Nat) (xs : List Nat),
      List.foldl Nat.max 0 (x :: xs) = Nat.max x (List.foldl Nat.max 0 xs) := by
  have swap : ∀ s x a : Nat, Nat.max (Nat.max s x) a = Nat.max (Nat.max s a) x := by
    intro s x a
    simp only [Nat.max_def]
    split_ifs <;> omega
  have L : ∀ (xs : List Nat) (s x : Nat),
      List.foldl Nat.max (Nat.max s x) xs = Nat.max x (List.foldl Nat.max s xs) := by
    intro xs
    induction xs with
    | nil =>
        intro s x
        simp only [List.foldl_nil, Nat.max_def]
        split_ifs <;> omega
    | cons a xs ih =>
        intro s x
        simp only [List.foldl_cons]
        rw [swap, ih]
  intro x xs
  simpa using L xs 0 x

theorem subseq_leq_size {X : Type u} [DecidableEq X] :
    ∀ (xs ys : List X),
      xs.Nodup →
      (∀ x, x ∈ xs → x ∈ ys) →
      xs.length ≤ ys.length := by
  intro xs ys UNIQ SUB
  exact (List.subperm_of_subset UNIQ SUB).length_le

end Prosa.Classic.Util.List
