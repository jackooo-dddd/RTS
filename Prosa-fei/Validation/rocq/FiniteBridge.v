From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype.
Require Import Relations.

Section FiniteExistentialBridge.
  Variables (CoreR CoreL : finType).
  Variables (toL : CoreR -> CoreL) (toR : CoreL -> CoreR).
  Hypothesis toR_toL : cancel toL toR.
  Hypothesis toL_toR : cancel toR toL.

  Variables (pR : pred CoreR) (pL : pred CoreL).
  Hypothesis predicate_rel : forall cR, pR cR = pL (toL cR).

  Lemma finite_exists_bridge :
    [exists cR : CoreR, pR cR] = [exists cL : CoreL, pL cL].
  Proof.
    apply/idP/idP.
    - move/existsP=> [cR HcR].
      apply/existsP; exists (toL cR).
      by rewrite -predicate_rel.
    - move/existsP=> [cL HcL].
      apply/existsP; exists (toR cL).
      rewrite predicate_rel toL_toR.
      exact HcL.
  Qed.
End FiniteExistentialBridge.
