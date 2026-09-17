-- Translated from: ../rt-proofs/classic/util/seqset.v
import Prosa.Util.Seqset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace Prosa.Classic.Util.Seqset

open Prosa.Util.Seqset

section Lemmas

variable {T : Type _} [DecidableEq T]
variable (s : SeqSet T)

theorem set_mem : ∀ x, (x ∈ s) ↔ (x ∈ s._set_seq) := by
    intro x
    exact Iff.rfl

end Lemmas

section LemmasFinType

variable {T : Type _} [DecidableEq T] [Fintype T]
variable (s : SeqSet T)

theorem set_card : s._set_seq.toFinset.card = s._set_seq.length := by
    rw [List.toFinset_card_of_nodup s.set_seq_uniq]

end LemmasFinType

end Prosa.Classic.Util.Seqset
