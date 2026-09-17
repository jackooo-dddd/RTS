-- Translated from: classic/util/notation.v
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Prosa.Util.Notation

namespace Prosa.Classic.Util.Notation

section Pair

  variable {A B : Type _}

  def pair_1st (p : A × B) : A := p.1
  def pair_2nd (p : A × B) : B := p.2

end Pair

section Triple

  variable {A B C : Type _}

  def triple_1st (p : (A × B) × C) : A := p.1.1
  def triple_2nd (p : (A × B) × C) : B := p.1.2
  def triple_3rd (p : (A × B) × C) : C := p.2

end Triple

def make_sequence {T : Type _} (opt : Option T) : List T :=
  match opt with
  | some j => [j]
  | none => []

def sumPairList {α : Type _} (r : List (α × α)) (F : α → α → ℕ) : ℕ :=
  r.foldl (fun acc p => acc + F p.1 p.2) 0

def sumPairListCond {α : Type _} (r : List (α × α)) (P : α → α → Bool) (F : α → α → ℕ) : ℕ :=
  r.foldl (fun acc p => if P p.1 p.2 then acc + F p.1 p.2 else acc) 0

def maxPairList {α : Type _} (r : List (α × α)) (F : α → α → ℕ) : ℕ :=
  r.foldl (fun acc p => max acc (F p.1 p.2)) 0

def maxPairListCond {α : Type _} (r : List (α × α)) (P : α → α → Bool) (F : α → α → ℕ) : ℕ :=
  r.foldl (fun acc p => if P p.1 p.2 then max acc (F p.1 p.2) else acc) 0

def filterPairs {α β : Type _} (s : List (α × β)) (C : α → β → Bool) : List (α × β) :=
  s.filter (fun p => C p.1 p.2)

def mapPairs {α β γ : Type _} (s : List α) (E : α → β) (F : α → γ) : List (β × γ) :=
  s.map (fun x => (E x, F x))

def memOptList {T : Type _} [BEq T] (x : T) (A : Option (List T)) : Bool :=
  match A with
  | some B => B.elem x
  | none => false

end Prosa.Classic.Util.Notation
