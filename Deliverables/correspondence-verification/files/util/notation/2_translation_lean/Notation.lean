-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/notation.v

import Mathlib.Data.List.Basic

namespace Prosa.Util.Notation

universe u v

/-- Convert a constant into a function that ignores its argument. -/
def constant {X : Type u} {Y : Type v} (c : Y) : X → Y := fun _ => c

/- The following helpers give Lean names to the source file's big-concatenation
notations. They are marked as Lean helpers rather than additional translated
public declarations. -/

/-- LEAN_HELPER: big concatenation over `[m, n)`. -/
def bigCat {α : Type u} (m n : Nat) (F : Nat → List α) : List α :=
  ((List.range (n - m)).map fun i => F (m + i)).flatten

/-- LEAN_HELPER: filtered big concatenation over `[m, n)`. -/
def bigCatCond {α : Type u} (m n : Nat) (P : Nat → Bool)
    (F : Nat → List α) : List α :=
  ((List.range (n - m)).filterMap fun i =>
    let index := m + i
    if P index then some (F index) else none).flatten

/-- LEAN_HELPER: big concatenation over `[0, n)`. -/
def bigCatOrd {α : Type u} (n : Nat) (F : Nat → List α) : List α :=
  ((List.range n).map F).flatten

/-- LEAN_HELPER: filtered big concatenation over `[0, n)`. -/
def bigCatOrdCond {α : Type u} (n : Nat) (P : Nat → Bool)
    (F : Nat → List α) : List α :=
  ((List.range n).filterMap fun i =>
    if P i then some (F i) else none).flatten

end Prosa.Util.Notation
