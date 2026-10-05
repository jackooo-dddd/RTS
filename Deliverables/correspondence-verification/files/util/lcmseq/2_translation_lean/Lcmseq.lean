-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/lcmseq.v

import Mathlib.Data.Nat.GCD.Basic
import Prosa.Util.Tactics

namespace Prosa.Util.Lcmseq

/-- Least common multiple of all entries of a sequence. -/
def lcml (xs : List Nat) : Nat :=
  xs.foldr Nat.lcm 1

/-- Every newly prepended entry divides the list LCM. -/
theorem int_divides_lcm_in_seq (x : Nat) (xs : List Nat) :
    x ∣ lcml (x :: xs) := by
  exact Nat.dvd_lcm_left x (lcml xs)

/-- The old list LCM divides the LCM after prepending an entry. -/
theorem lcm_seq_divides_lcm_super (x : Nat) (xs : List Nat) :
    lcml xs ∣ lcml (x :: xs) := by
  exact Nat.dvd_lcm_right x (lcml xs)

/-- Every member of a sequence divides its list LCM. -/
theorem lcm_seq_is_mult_of_all_ints (x : Nat) (xs : List Nat)
    (hx : x ∈ xs) : x ∣ lcml xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [lcml, List.foldr_cons]
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.dvd_lcm_left x (List.foldr Nat.lcm 1 ys)
      · exact (ih hx).trans (Nat.dvd_lcm_right y (List.foldr Nat.lcm 1 ys))

/-- A list containing only positive naturals has positive list LCM. -/
theorem all_pos_implies_lcml_pos (xs : List Nat)
    (hpos : ∀ x, x ∈ xs → 0 < x) : 0 < lcml xs := by
  induction xs with
  | nil => simp [lcml]
  | cons x xs ih =>
      simp only [lcml, List.foldr_cons]
      exact Nat.lcm_pos (hpos x (by simp))
        (ih (fun y hy => hpos y (by simp [hy])))

end Prosa.Util.Lcmseq
