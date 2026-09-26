import Validation.fixtures.translation_order.ScheduleComputationInterface

/-!
Validation-only interface for certificates that quantify over processor
models inside a statement (`… → ∀ PState : ProcessorState Job, …`).

`fintypeOfNodupListing` is the `Fintype` whose `elems` is exactly a given
duplicate-free complete listing, so a certificate can transport a Rocq
processor model (whose `finType` enumeration is such a listing) to a Lean one
whose finite folds and sums compute along that listing. Its body only packages
the listing and the two proofs (`Multiset.Nodup ↑l` and `c ∈ ⟨↑l, _⟩` are
definitionally `l.Nodup` and `c ∈ l`). Nothing here is a production
declaration.
-/

namespace Prosa.Validation.ProcessorStateCoverInterface

universe w

/-- The `Fintype` whose elements are exactly a duplicate-free complete listing. -/
def fintypeOfNodupListing {C : Type w} (l : List C) (hnd : l.Nodup) (hc : ∀ c, c ∈ l) :
    Fintype C :=
  ⟨⟨(l : Multiset C), hnd⟩, hc⟩

end Prosa.Validation.ProcessorStateCoverInterface
