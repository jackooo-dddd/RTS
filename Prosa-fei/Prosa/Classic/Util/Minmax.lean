-- Translated from: ../rt-proofs/classic/util/minmax.v
import Mathlib
import Prosa.Util.Minmax
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Minmax

open List

section MinMaxSeq

section ArgGeneric

variable {T1 T2 : Type _} [DecidableEq T1] [DecidableEq T2]

def seq_argmin (rel : T2 → T2 → Bool) (F : T1 → T2) : List T1 → Option T1
  | [] => none
  | x :: l' =>
    match seq_argmin rel F l' with
    | some y => if rel (F x) (F y) then some x else some y
    | none => some x

def seq_argmax (rel : T2 → T2 → Bool) (F : T1 → T2) : List T1 → Option T1
  | [] => none
  | x :: l' =>
    match seq_argmax rel F l' with
    | some y => if rel (F y) (F x) then some x else some y
    | none => some x

variable (rel : T2 → T2 → Bool)
variable (F : T1 → T2)

section Lemmas

theorem seq_argmin_exists (l : List T1) (x : T1) :
    x ∈ l → seq_argmin rel F l ≠ none := by
  induction l with
  | nil => intro h; simp at h
  | cons a l' ih =>
    intro _
    simp only [seq_argmin]
    cases seq_argmin rel F l' with
    | none => simp
    | some y => simp; split <;> simp

theorem seq_argmin_in_seq (l : List T1) (x : T1) :
    seq_argmin rel F l = some x → x ∈ l := by
  induction l with
  | nil => simp [seq_argmin]
  | cons a l' ih =>
    simp only [seq_argmin]
    cases hm : seq_argmin rel F l' with
    | none =>
      intro h; have := Option.some.inj h; subst this; exact List.Mem.head _
    | some y =>
      simp only
      split_ifs
      · intro h; have := Option.some.inj h; subst this; exact List.Mem.head _
      · intro h; have hxy := Option.some.inj h; subst hxy
        exact List.Mem.tail _ (ih hm)

theorem seq_argmax_exists (l : List T1) (x : T1) :
    x ∈ l → seq_argmax rel F l ≠ none := by
  induction l with
  | nil => intro h; simp at h
  | cons a l' ih =>
    intro _
    simp only [seq_argmax]
    cases seq_argmax rel F l' with
    | none => simp
    | some y => simp; split <;> simp

theorem seq_argmax_in_seq (l : List T1) (x : T1) :
    seq_argmax rel F l = some x → x ∈ l := by
  induction l with
  | nil => simp [seq_argmax]
  | cons a l' ih =>
    simp only [seq_argmax]
    cases hm : seq_argmax rel F l' with
    | none =>
      intro h; have := Option.some.inj h; subst this; exact List.Mem.head _
    | some y =>
      simp only
      split_ifs
      · intro h; have := Option.some.inj h; subst this; exact List.Mem.head _
      · intro h; have hxy := Option.some.inj h; subst hxy
        exact List.Mem.tail _ (ih hm)

section TotalOrder

variable (H_transitive : ∀ x y z : T2, rel x y = true → rel y z = true → rel x z = true)
variable (l : List T1)
variable (H_total_over_list : ∀ x y : T1,
    x ∈ l → y ∈ l → rel (F x) (F y) = true ∨ rel (F y) (F x) = true)
include H_transitive H_total_over_list

theorem seq_argmin_computes_min (x y : T1) :
    seq_argmin rel F l = some x →
    y ∈ l →
    rel (F x) (F y) = true := by
  revert x y
  induction l with
  | nil => intro _ _ _ h; simp at h
  | cons a l' ih =>
    intro x y hmin hy
    simp only [seq_argmin] at hmin
    cases harg : seq_argmin rel F l' with
    | none =>
      rw [harg] at hmin
      have hxa := Option.some.inj hmin; subst hxa
      cases hy with
      | head =>
        have htot := H_total_over_list a a List.mem_cons_self List.mem_cons_self
        rcases htot with h | h <;> exact h
      | tail _ hy' =>
        exact absurd harg (seq_argmin_exists rel F l' y hy')
    | some s =>
      rw [harg] at hmin
      simp only at hmin
      split_ifs at hmin with hrel
      · have hxa := Option.some.inj hmin; subst hxa
        cases hy with
        | head =>
          have htot := H_total_over_list a a List.mem_cons_self List.mem_cons_self
          rcases htot with h | h <;> exact h
        | tail _ hy' =>
          have ih_result := ih (fun x' y' hx' hy' => H_total_over_list x' y' (List.mem_cons_of_mem a hx') (List.mem_cons_of_mem a hy')) s y harg hy'
          exact H_transitive _ _ _ hrel ih_result
      · have hxs := Option.some.inj hmin; subst hxs
        cases hy with
        | head =>
          have hs_in := seq_argmin_in_seq rel F l' s harg
          have htot := H_total_over_list a s List.mem_cons_self (List.mem_cons_of_mem a hs_in)
          rcases htot with h | h
          · exfalso; exact hrel h
          · exact h
        | tail _ hy' =>
          exact ih (fun x' y' hx' hy' => H_total_over_list x' y' (List.mem_cons_of_mem a hx') (List.mem_cons_of_mem a hy')) s y harg hy'

theorem seq_argmax_computes_max (x y : T1) :
    seq_argmax rel F l = some x →
    y ∈ l →
    rel (F y) (F x) = true := by
  revert x y
  induction l with
  | nil => intro _ _ _ h; simp at h
  | cons a l' ih =>
    intro x y hmax hy
    simp only [seq_argmax] at hmax
    cases harg : seq_argmax rel F l' with
    | none =>
      rw [harg] at hmax
      have hxa := Option.some.inj hmax; subst hxa
      cases hy with
      | head =>
        have htot := H_total_over_list a a List.mem_cons_self List.mem_cons_self
        rcases htot with h | h <;> exact h
      | tail _ hy' =>
        exact absurd harg (seq_argmax_exists rel F l' y hy')
    | some s =>
      rw [harg] at hmax
      simp only at hmax
      split_ifs at hmax with hrel
      · have hxa := Option.some.inj hmax; subst hxa
        cases hy with
        | head =>
          have htot := H_total_over_list a a List.mem_cons_self List.mem_cons_self
          rcases htot with h | h <;> exact h
        | tail _ hy' =>
          have ih_result := ih (fun x' y' hx' hy' => H_total_over_list x' y' (List.mem_cons_of_mem a hx') (List.mem_cons_of_mem a hy')) s y harg hy'
          exact H_transitive _ _ _ ih_result hrel
      · have hxs := Option.some.inj hmax; subst hxs
        cases hy with
        | head =>
          have hs_in := seq_argmax_in_seq rel F l' s harg
          have htot := H_total_over_list a s List.mem_cons_self (List.mem_cons_of_mem a hs_in)
          rcases htot with h | h
          · exact h
          · exfalso; exact hrel h
        | tail _ hy' =>
          exact ih (fun x' y' hx' hy' => H_total_over_list x' y' (List.mem_cons_of_mem a hx') (List.mem_cons_of_mem a hy')) s y harg hy'

end TotalOrder

end Lemmas

end ArgGeneric

section MinGeneric

variable {T : Type _} [DecidableEq T]
variable (rel : T → T → Bool)

def seq_min (l : List T) : Option T := seq_argmin rel id l
def seq_max (l : List T) : Option T := seq_argmax rel id l

section Lemmas

theorem seq_min_exists (l : List T) (x : T) :
    x ∈ l → seq_min rel l ≠ none := by
  exact seq_argmin_exists rel id l x

theorem seq_min_in_seq (l : List T) (x : T) :
    seq_min rel l = some x → x ∈ l := by
  exact seq_argmin_in_seq rel id l x

theorem seq_max_exists (l : List T) (x : T) :
    x ∈ l → seq_max rel l ≠ none := by
  exact seq_argmax_exists rel id l x

theorem seq_max_in_seq (l : List T) (x : T) :
    seq_max rel l = some x → x ∈ l := by
  exact seq_argmax_in_seq rel id l x

section TotalOrder

variable (H_transitive : ∀ x y z : T, rel x y = true → rel y z = true → rel x z = true)
variable (l : List T)
variable (H_total_over_list : ∀ x y : T,
    x ∈ l → y ∈ l → rel x y = true ∨ rel y x = true)
include H_transitive H_total_over_list

theorem seq_min_computes_min (x y : T) :
    seq_min rel l = some x →
    y ∈ l →
    rel x y = true := by
  intro h1 h2
  exact seq_argmin_computes_min rel id H_transitive l
    (fun x' y' hx' hy' => H_total_over_list x' y' hx' hy') x y h1 h2

theorem seq_max_computes_max (x y : T) :
    seq_max rel l = some x →
    y ∈ l →
    rel y x = true := by
  intro h1 h2
  exact seq_argmax_computes_max rel id H_transitive l
    (fun x' y' hx' hy' => H_total_over_list x' y' hx' hy') x y h1 h2

end TotalOrder

end Lemmas

end MinGeneric

section ArgNat

variable {T : Type _} [DecidableEq T]
variable (F : T → ℕ)

def seq_argmin_nat (l : List T) : Option T := seq_argmin (fun a b => a ≤ b) F l
def seq_argmax_nat (l : List T) : Option T := seq_argmax (fun a b => a ≤ b) F l

section Lemmas

theorem seq_argmin_nat_exists (l : List T) (x : T) :
    x ∈ l → seq_argmin_nat F l ≠ none := by
  exact seq_argmin_exists (fun a b => a ≤ b) F l x

theorem seq_argmin_nat_in_seq (l : List T) (x : T) :
    seq_argmin_nat F l = some x → x ∈ l := by
  exact seq_argmin_in_seq (fun a b => a ≤ b) F l x

theorem seq_argmax_nat_exists (l : List T) (x : T) :
    x ∈ l → seq_argmax_nat F l ≠ none := by
  exact seq_argmax_exists (fun a b => a ≤ b) F l x

theorem seq_argmax_nat_in_seq (l : List T) (x : T) :
    seq_argmax_nat F l = some x → x ∈ l := by
  exact seq_argmax_in_seq (fun a b => a ≤ b) F l x

section TotalOrder

theorem seq_argmin_nat_computes_min (l : List T) (x y : T) :
    seq_argmin_nat F l = some x →
    y ∈ l →
    F x ≤ F y := by
  intro h1 h2
  unfold seq_argmin_nat at h1
  have := seq_argmin_computes_min (fun a b => a ≤ b) F
    (fun x1 x2 x3 h1 h2 => by simp [decide_eq_true_eq] at *; omega) l
    (fun x' y' _ _ => by simp [decide_eq_true_eq]; omega) x y h1 h2
  simp [decide_eq_true_eq] at this
  exact this

theorem seq_argmax_nat_computes_max (l : List T) (x y : T) :
    seq_argmax_nat F l = some x →
    y ∈ l →
    F x ≥ F y := by
  intro h1 h2
  unfold seq_argmax_nat at h1
  have := seq_argmax_computes_max (fun a b => a ≤ b) F
    (fun x1 x2 x3 h1 h2 => by simp [decide_eq_true_eq] at *; omega) l
    (fun x' y' _ _ => by simp [decide_eq_true_eq]; omega) x y h1 h2
  simp [decide_eq_true_eq] at this
  exact this

end TotalOrder

end Lemmas

end ArgNat

section MinNat

def seq_min_nat (l : List ℕ) : Option ℕ := seq_argmin (fun a b => a ≤ b) id l
def seq_max_nat (l : List ℕ) : Option ℕ := seq_argmax (fun a b => a ≤ b) id l

section Lemmas

theorem seq_min_nat_exists (l : List ℕ) (x : ℕ) :
    x ∈ l → seq_min_nat l ≠ none := by
  exact seq_argmin_exists (fun a b => a ≤ b) id l x

theorem seq_min_nat_in_seq (l : List ℕ) (x : ℕ) :
    seq_min_nat l = some x → x ∈ l := by
  exact seq_argmin_in_seq (fun a b => a ≤ b) id l x

theorem seq_max_nat_exists (l : List ℕ) (x : ℕ) :
    x ∈ l → seq_max_nat l ≠ none := by
  exact seq_argmax_exists (fun a b => a ≤ b) id l x

theorem seq_max_nat_in_seq (l : List ℕ) (x : ℕ) :
    seq_max_nat l = some x → x ∈ l := by
  exact seq_argmax_in_seq (fun a b => a ≤ b) id l x

section TotalOrder

theorem seq_min_nat_computes_min (l : List ℕ) (x y : ℕ) :
    seq_min_nat l = some x →
    y ∈ l →
    x ≤ y := by
  intro h1 h2
  unfold seq_min_nat at h1
  have := seq_argmin_computes_min (fun a b => a ≤ b) id
    (fun x1 x2 x3 h1 h2 => by simp [decide_eq_true_eq] at *; omega) l
    (fun x' y' _ _ => by simp [decide_eq_true_eq]; omega) x y h1 h2
  simp [decide_eq_true_eq] at this
  exact this

theorem seq_max_nat_computes_max (l : List ℕ) (x y : ℕ) :
    seq_max_nat l = some x →
    y ∈ l →
    x ≥ y := by
  intro h1 h2
  unfold seq_max_nat at h1
  have := seq_argmax_computes_max (fun a b => a ≤ b) id
    (fun x1 x2 x3 h1 h2 => by simp [decide_eq_true_eq] at *; omega) l
    (fun x' y' _ _ => by simp [decide_eq_true_eq]; omega) x y h1 h2
  simp [decide_eq_true_eq] at this
  exact this

end TotalOrder

end Lemmas

end MinNat

section NatRange

def values_between (a b : ℕ) : List ℕ :=
  (List.finRange b).map (fun i => i.val) |>.filter (fun x => x ≥ a)

theorem mem_values_between (a b : ℕ) (x : ℕ) :
    x ∈ values_between a b ↔ a ≤ x ∧ x < b := by
  simp only [values_between, List.mem_filter, List.mem_map, List.mem_finRange, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨i, hi⟩, _, rfl⟩, hge⟩
    exact ⟨hge, hi⟩
  · rintro ⟨hge, hlt⟩
    exact ⟨⟨⟨x, hlt⟩, trivial, rfl⟩, hge⟩

def min_nat_cond (P : ℕ → Bool) (a b : ℕ) : Option ℕ :=
  seq_min_nat ((values_between a b).filter P)

def max_nat_cond (P : ℕ → Bool) (a b : ℕ) : Option ℕ :=
  seq_max_nat ((values_between a b).filter P)

theorem min_nat_cond_exists (P : ℕ → Bool) (a b : ℕ) (x : ℕ) :
    a ≤ x ∧ x < b →
    P x = true →
    min_nat_cond P a b ≠ none := by
  intro ⟨hge, hlt⟩ hP
  apply seq_min_nat_exists _ x
  rw [List.mem_filter]
  exact ⟨(mem_values_between a b x).mpr ⟨hge, hlt⟩, by simp [hP]⟩

theorem min_nat_cond_in_seq (P : ℕ → Bool) (a b : ℕ) (x : ℕ) :
    min_nat_cond P a b = some x →
    a ≤ x ∧ x < b ∧ P x = true := by
  intro h
  have hx := seq_min_nat_in_seq _ x h
  rw [List.mem_filter] at hx
  have hv := (mem_values_between a b x).mp hx.1
  exact ⟨hv.1, hv.2, by simpa using hx.2⟩

theorem min_nat_cond_computes_min (P : ℕ → Bool) (a b : ℕ) (x : ℕ) :
    min_nat_cond P a b = some x →
    ∀ y, a ≤ y ∧ y < b → P y = true → x ≤ y := by
  intro h y ⟨hge, hlt⟩ hP
  exact seq_min_nat_computes_min _ x y h
    (List.mem_filter.mpr ⟨(mem_values_between a b y).mpr ⟨hge, hlt⟩, by simp [hP]⟩)

theorem max_nat_cond_exists (P : ℕ → Bool) (a b : ℕ) (x : ℕ) :
    a ≤ x ∧ x < b →
    P x = true →
    max_nat_cond P a b ≠ none := by
  intro ⟨hge, hlt⟩ hP
  apply seq_max_nat_exists _ x
  rw [List.mem_filter]
  exact ⟨(mem_values_between a b x).mpr ⟨hge, hlt⟩, by simp [hP]⟩

theorem max_nat_cond_in_seq (P : ℕ → Bool) (a b : ℕ) (x : ℕ) :
    max_nat_cond P a b = some x →
    a ≤ x ∧ x < b ∧ P x = true := by
  intro h
  have hx := seq_max_nat_in_seq _ x h
  rw [List.mem_filter] at hx
  have hv := (mem_values_between a b x).mp hx.1
  exact ⟨hv.1, hv.2, by simpa using hx.2⟩

theorem max_nat_cond_computes_max (P : ℕ → Bool) (a b : ℕ) (x : ℕ) :
    max_nat_cond P a b = some x →
    ∀ y, a ≤ y ∧ y < b → P y = true → y ≤ x := by
  intro h y ⟨hge, hlt⟩ hP
  exact seq_max_nat_computes_max _ x y h
    (List.mem_filter.mpr ⟨(mem_values_between a b y).mpr ⟨hge, hlt⟩, by simp [hP]⟩)

end NatRange

end MinMaxSeq

section Kmin

variable {T1 T2 : Type _} [DecidableEq T1] [DecidableEq T2]

def seq_argmin_k (rel : T2 → T2 → Bool) (F : T1 → T2) : List T1 → ℕ → List T1
  | _, 0 => []
  | l, k + 1 =>
    match seq_argmin rel F l with
    | some min_x =>
      let l_without_min := l.erase min_x
      min_x :: seq_argmin_k rel F l_without_min k
    | none => []

variable (rel : T2 → T2 → Bool)
variable (F : T1 → T2)

theorem seq_argmin_k_exists (k : ℕ) (l : List T1) (x : T1) :
    k > 0 → x ∈ l → seq_argmin_k rel F l k ≠ [] := by
  intro hk hx
  cases k with
  | zero => omega
  | succ k' =>
    simp only [seq_argmin_k]
    have hne := seq_argmin_exists rel F l x hx
    cases harg : seq_argmin rel F l with
    | none => simp [harg] at hne
    | some min_x => simp

end Kmin

end Prosa.Classic.Util.Minmax
