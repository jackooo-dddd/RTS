-- Translated from: ../rt-proofs/classic/util/powerset.v
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Basic
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Powerset

section PowerSet

def powerset {T : Type _} [DecidableEq T] (l : List T) : List (List T) :=
  l.sublists

lemma mem_powerset {T : Type _} [DecidableEq T] (x : List T) (y : List T)
    (h : y ∈ powerset x) : ∀ z, z ∈ y → z ∈ x := by
  intro z hz
  unfold powerset at h
  rw [List.mem_sublists] at h
  exact h.subset hz

end PowerSet

end Prosa.Classic.Util.Powerset
