-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/poet.v

import Prosa.Util.List

namespace Prosa.Util.Poet

/--
A pointwise Boolean check over a zip supplies, for every member of the left
list, a witness from the right list.  This preserves the source's ordered
`seq`/`zip` semantics; no extensional finite-set representation is involved.
-/
theorem forall_exists_implied_by_forall_in_zip
    {X Y : Type _} [DecidableEq X] [DecidableEq Y]
    (PBool : X × Y → Bool) (PProp : X → Y → Prop) (xs : List X)
    (hrel : ∀ x y, PBool (x, y) = true ↔ PProp x y)
    (hzip : ∃ ys : List Y,
      xs.length = ys.length ∧ (xs.zip ys).all PBool = true) :
    ∀ x, x ∈ xs → ∃ y, PProp x y := by
  obtain ⟨ys, hlen, hall⟩ := hzip
  intro x hx
  have hidx : xs.idxOf x < xs.length := List.idxOf_lt_length_of_mem hx
  have hidxY : xs.idxOf x < ys.length := by simpa [← hlen] using hidx
  let y := ys[xs.idxOf x]
  have hxy : (x, y) ∈ xs.zip ys := by
    apply Prosa.Util.List.in_zip xs ys x x y y hlen
    refine ⟨xs.idxOf x, hidx, ?_, ?_⟩
    · simp [List.getD, hidx, List.getElem_idxOf hidx]
    · simp [List.getD, hidxY, y]
  refine ⟨y, (hrel x y).mp ?_⟩
  exact (List.all_eq_true.mp hall) (x, y) hxy

end Prosa.Util.Poet
