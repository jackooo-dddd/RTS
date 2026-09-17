-- Translated from: ../rt-proofs/util/notation.v
import Mathlib.Data.List.Basic

namespace Prosa.Util.Notation

/-- Big concatenation over a range `[m, n)`. -/
def bigCat {α : Type _} (m n : ℕ) (F : ℕ → List α) : List α :=
  ((List.range (n - m)).map (fun i => F (m + i))).flatten

/-- Big concatenation over a range `[m, n)` with a filter. -/
def bigCatCond {α : Type _} (m n : ℕ) (P : ℕ → Bool) (F : ℕ → List α) : List α :=
  ((List.range (n - m)).filterMap (fun i =>
    let idx := m + i
    if P idx then some (F idx) else none)).flatten

/-- Big concatenation over a range `[0, n)`. -/
def bigCatOrd {α : Type _} (n : ℕ) (F : ℕ → List α) : List α :=
  ((List.range n).map F).flatten

/-- Big concatenation over a range `[0, n)` with a filter. -/
def bigCatOrdCond {α : Type _} (n : ℕ) (P : ℕ → Bool) (F : ℕ → List α) : List α :=
  ((List.range n).filterMap (fun i =>
    if P i then some (F i) else none)).flatten

end Prosa.Util.Notation
