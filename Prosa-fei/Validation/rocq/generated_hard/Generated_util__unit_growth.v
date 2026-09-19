From mathcomp Require Import ssreflect ssrbool eqtype ssrnat zify.zify.
Require Import prosa.util.tactics prosa.util.notation prosa.util.rel.

Module Generated_util__unit_growth.

Section ExtractedContext_0.
    Variable P : nat -> bool.
    Variables t1 t2 : nat.
    Hypothesis H_t1_le_t2 : t1 <= t2.
    Hypothesis H_not_P_at_t1 : ~~ P t1.
    Hypothesis H_P_at_t2 : P t2.

    Lemma exists_first_intermediate_point :
      exists t, (t1 < t <= t2) /\ (forall x, t1 <= x < t -> ~~ P x) /\ P t.
    Proof.
      have EX: exists x, P x && (t1 < x <= t2).
      { exists t2.
        apply/andP; split; first by done.
        apply/andP; split; last by done.
        move: H_t1_le_t2; rewrite leq_eqVlt => /orP [/eqP EQ | NEQ1]; last by done.
        by exfalso; subst t2; move: H_not_P_at_t1 => /negP NPt1.
      }
      have MIN := ex_minnP EX.
      move: MIN => [x /andP [Px /andP [LT1 LT2]] MIN]; clear EX.
      exists x; repeat split; [ apply/andP; split | | ]; try done.
      move => y /andP [NEQ1 NEQ2]; apply/negPn; intros Py.
      feed (MIN y).
      { apply/andP; split; first by done.
        apply/andP; split.
        - move: NEQ1. rewrite leq_eqVlt => /orP [/eqP EQ | NEQ1]; last by done.
          by exfalso; subst y; move: H_not_P_at_t1 => /negP NPt1.
        - by apply ltnW, leq_trans with x.
      }
      by move: NEQ2; rewrite ltnNge => /negP NEQ2.
    Qed.

End ExtractedContext_0.

End Generated_util__unit_growth.

Check @Generated_util__unit_growth.exists_first_intermediate_point.
Print Assumptions Generated_util__unit_growth.exists_first_intermediate_point.
