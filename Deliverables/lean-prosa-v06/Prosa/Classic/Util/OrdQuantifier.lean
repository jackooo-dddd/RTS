-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/ord_quantifier.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 11)

import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Basic

/-!
Lemmas about Boolean quantifiers over ordinals.

Representation notes: `'I_n` is `Fin n`; `ord_max : 'I_n.+1` is `Fin.last n`;
`widen_ord (leqnSn n)` is `Fin.castSucc`.  The finite Boolean quantifiers
`[exists x in 'I_n, P x]` / `[forall x in 'I_n, P x]` are the direct Boolean
enumerations `(List.finRange n).any P` / `(List.finRange n).all P`.  The source's
Ltac helpers `simpl_exists_ord` / `simpl_forall_ord` have no Lean counterpart.
-/

namespace Prosa.Classic.Util.OrdQuantifier

theorem exists_ord0 :
    ∀ P : Fin 0 → Bool,
      (List.finRange 0).any P = false := by
  intro P
  rfl

theorem exists_recr :
    ∀ (n : Nat) (P : Fin (n + 1) → Bool),
      (List.finRange (n + 1)).any P =
        ((List.finRange n).any (fun x => P (Fin.castSucc x)) || P (Fin.last n)) := by
  intro n P
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.or_eq_true]
  exact Fin.exists_fin_succ'

theorem forall_ord0 :
    ∀ P : Fin 0 → Bool,
      (List.finRange 0).all P = true := by
  intro P
  rfl

theorem forall_recr :
    ∀ (n : Nat) (P : Fin (n + 1) → Bool),
      (List.finRange (n + 1)).all P =
        ((List.finRange n).all (fun x => P (Fin.castSucc x)) && P (Fin.last n)) := by
  intro n P
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true]
  exact Fin.forall_fin_succ'

end Prosa.Classic.Util.OrdQuantifier
