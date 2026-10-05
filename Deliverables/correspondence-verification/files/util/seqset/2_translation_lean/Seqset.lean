-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/seqset.v

import Mathlib.Data.List.Basic

namespace Prosa.Util.Seqset

universe u

/-- A source `set` is an ordered sequence together with a no-duplicates law.
It is intentionally not represented by `Finset`, since sequence order remains
observable through the source coercion to `seq`. -/
structure set (T : Type u) [DecidableEq T] where
  val : List T
  nodup : val.Nodup

instance {T : Type u} [DecidableEq T] : Coe (set T) (List T) where
  coe s := s.val

instance {T : Type u} [DecidableEq T] : Membership T (set T) where
  mem s x := x ∈ s.val

instance {T : Type u} [DecidableEq T] : DecidableEq (set T) := fun a b =>
  if h : a.val = b.val then
    isTrue (by cases a; cases b; cases h; rfl)
  else
    isFalse (fun hab => h (congrArg set.val hab))

/-- The source's phantom-argument alias, represented directly at the Lean
type boundary. -/
abbrev set_of (T : Type u) [DecidableEq T] := set T

/-- Elements stored in a sequence-set are unique. -/
theorem set_uniq {T : Type u} [DecidableEq T] (s : set T) : s.val.Nodup :=
  s.nodup

end Prosa.Util.Seqset
