import Prosa.Classic.Util.Bigord

/-!
Validation-only interface for `classic/util/bigord.v` (classic family): kernel-checked Lean
equations, exported with their proofs, that read the ordinal enumeration `List.finRange n` of
the translation through `Fin.val` as `List.range' 0 n`, which the Rocq certificate relates
structurally to MathComp's `iota 0 n`.  Used as propositional equations (transport) only.
-/

namespace Prosa.Validation.ClassicBigordInterface

/-- The ordinal values shifted by `s` are `s, s + 1, …, s + n - 1`. -/
theorem finRange_map_shift (n : Nat) : ∀ s : Nat,
    (List.finRange n).map (fun i => s + i.val) = List.range' s n := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      rw [List.finRange_succ, List.map_cons, List.map_map, List.range'_succ]
      have h : ((fun i : Fin (n + 1) => s + i.val) ∘ (Fin.succ : Fin n → Fin (n + 1))) =
          (fun i : Fin n => (s + 1) + i.val) := by
        funext i
        show s + (i.val + 1) = s + 1 + i.val
        rw [Nat.add_assoc, Nat.add_comm i.val 1]
      rw [h, ih (s + 1)]
      rfl

/-- The ordinal values are `0, 1, …, n - 1`. -/
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  have h := finRange_map_shift n 0
  have e : (fun i : Fin n => 0 + i.val) = Fin.val := by
    funext i
    exact Nat.zero_add i.val
  rw [e] at h
  exact h

end Prosa.Validation.ClassicBigordInterface
