-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/seqset.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 5)

import Prosa.Util.Seqset
import Mathlib.Data.Fintype.Card

/-!
The source re-exports `prosa.util.seqset` (imported above: the accepted v0.6
sequence-set `Prosa.Util.Seqset.set`) and proves two facts.

Representation notes:
* Boolean membership equalities `(x \in a) = (x \in b)` are written
  `decide (x ∈ a) = decide (x ∈ b)`, as in the accepted v0.6 translation.
* `Context {T : finType}` is a carrier with `[Fintype T] [DecidableEq T]`
  (v0.6 `finType` policy); MathComp's `#|s|` is the number of elements of `T`
  in `s`, i.e. `(Finset.univ.filter (· ∈ s)).card`.
-/

namespace Prosa.Classic.Util.Seqset

open Prosa.Util.Seqset

universe u

/-- LEAN_HELPER: membership in a sequence-set is decided on its sequence. -/
instance memDecidable {T : Type u} [DecidableEq T] (x : T) (s : set T) :
    Decidable (x ∈ s) :=
  inferInstanceAs (Decidable (x ∈ s.val))

/-- Membership in a set is membership in its underlying sequence. -/
theorem set_mem {T : Type u} [DecidableEq T] (s : set T) :
    ∀ x, decide (x ∈ s) = decide (x ∈ s.val) := by
  intro x
  rfl

/-- The cardinality of a set over a finite type is the size of its sequence. -/
theorem set_card {T : Type u} [Fintype T] [DecidableEq T] (s : set T) :
    (Finset.univ.filter (fun x => x ∈ s)).card = s.val.length := by
  have h : Finset.univ.filter (fun x => x ∈ s) = s.val.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    rfl
  rw [h, List.toFinset_card_of_nodup s.nodup]

end Prosa.Classic.Util.Seqset
