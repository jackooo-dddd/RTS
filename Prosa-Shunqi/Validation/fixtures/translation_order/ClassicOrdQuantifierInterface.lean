import Prosa.Classic.Util.OrdQuantifier

/-!
Validation-only interface for `classic/util/ord_quantifier.v` (classic family): kernel-checked
Lean equations, exported with their proofs, that read `any`/`all` over the ordinal enumeration
`List.finRange n` as `any`/`all` over `List.range' 0 n`, which the Rocq certificate relates
structurally to MathComp's `iota 0 n`.  Used as propositional equations (transport) only.
-/

namespace Prosa.Validation.ClassicOrdQuantifierInterface

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

theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  have h := finRange_map_shift n 0
  have e : (fun i : Fin n => 0 + i.val) = Fin.val := by
    funext i
    exact Nat.zero_add i.val
  rw [e] at h
  exact h

/-- `any` over all ordinals, read through `Fin.val`. -/
theorem finRange_any (n : Nat) (q : Fin n → Bool) :
    (List.finRange n).any q =
      (List.range' 0 n).any (fun k => if h : k < n then q ⟨k, h⟩ else false) := by
  rw [← finRange_map_val, List.any_map]
  congr 1
  funext i
  show q i = if h : i.val < n then q ⟨i.val, h⟩ else false
  rw [dif_pos i.isLt]

/-- `all` over all ordinals, read through `Fin.val`. -/
theorem finRange_all (n : Nat) (q : Fin n → Bool) :
    (List.finRange n).all q =
      (List.range' 0 n).all (fun k => if h : k < n then q ⟨k, h⟩ else true) := by
  rw [← finRange_map_val, List.all_map]
  congr 1
  funext i
  show q i = if h : i.val < n then q ⟨i.val, h⟩ else true
  rw [dif_pos i.isLt]

end Prosa.Validation.ClassicOrdQuantifierInterface
