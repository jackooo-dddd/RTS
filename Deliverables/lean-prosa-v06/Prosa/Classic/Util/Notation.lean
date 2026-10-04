-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/notation.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 4)

import Prosa.Util.Notation

/-!
The source re-exports `prosa.util.notation` (imported above), defines pair and
triple projections and an option-to-list wrapper, and declares notations for
big sums/maxima over lists of pairs, pair filters/maps and membership in an
optional list.  The notations become `LEAN_HELPER` definitions with the same
meaning: MathComp's `\sum_(i <- r) F` is `List.sum (r.map F)` (a right fold with
`+` and `0`), and `\max_(i <- r) F` is the right fold of `maxn` from `0`.

Representation note: Rocq's `A * B * C` is `(A * B) * C`; Lean's `×` associates
to the right, so triples are written `(A × B) × C`.
-/

namespace Prosa.Classic.Util.Notation

universe u v w

/-- First component of a pair. -/
def pair_1st {A : Type u} {B : Type v} (p : A × B) : A := p.1

/-- Second component of a pair. -/
def pair_2nd {A : Type u} {B : Type v} (p : A × B) : B := p.2

/-- First component of a triple.  (The source's explicit binder shadows the
section variable, so the section variable is not abstracted.) -/
def triple_1st {A : Type u} {B : Type v} {C : Type w} (p : (A × B) × C) : A := p.1.1

/-- Second component of a triple. -/
def triple_2nd {A : Type u} {B : Type v} {C : Type w} (p : (A × B) × C) : B := p.1.2

/-- Third component of a triple. -/
def triple_3rd {A : Type u} {B : Type v} {C : Type w} (p : (A × B) × C) : C := p.2

/-- Wrap an optional element into a list with at most one element. -/
def make_sequence {T : Type u} (opt : Option T) : List T :=
  match opt with
  | some j => [j]
  | none => []

/-- LEAN_HELPER: `\sum_((m, n) <- r) F`. -/
def sumPairs {A : Type u} {B : Type v} (r : List (A × B)) (F : A → B → Nat) : Nat :=
  (r.map fun i => F i.1 i.2).sum

/-- LEAN_HELPER: `\sum_((m, n) <- r | P) F`. -/
def sumPairsCond {A : Type u} {B : Type v} (r : List (A × B)) (P : A → B → Bool)
    (F : A → B → Nat) : Nat :=
  ((r.filter fun i => P i.1 i.2).map fun i => F i.1 i.2).sum

/-- LEAN_HELPER: `\max_((m, n) <- r) F`. -/
def maxPairs {A : Type u} {B : Type v} (r : List (A × B)) (F : A → B → Nat) : Nat :=
  (r.map fun i => F i.1 i.2).foldr Nat.max 0

/-- LEAN_HELPER: `\max_((m, n) <- r | P) F`. -/
def maxPairsCond {A : Type u} {B : Type v} (r : List (A × B)) (P : A → B → Bool)
    (F : A → B → Nat) : Nat :=
  ((r.filter fun i => P i.1 i.2).map fun i => F i.1 i.2).foldr Nat.max 0

/-- LEAN_HELPER: `[pairs (x, y) <- s | C]`. -/
def pairsFilter {A : Type u} {B : Type v} (s : List (A × B)) (C : A → B → Bool) :
    List (A × B) :=
  s.filter fun i => C i.1 i.2

/-- LEAN_HELPER: `[pairs (E, F) | x <- s]`. -/
def pairsMap {X : Type u} {A : Type v} {B : Type w} (E : X → A) (F : X → B)
    (s : List X) : List (A × B) :=
  s.map fun x => (E x, F x)

/-- LEAN_HELPER: `x \In A`, membership in an optional list (false for `None`). -/
def optIn {T : Type u} [DecidableEq T] (x : T) (A : Option (List T)) : Bool :=
  match A with
  | some B => decide (x ∈ B)
  | none => false

end Prosa.Classic.Util.Notation
