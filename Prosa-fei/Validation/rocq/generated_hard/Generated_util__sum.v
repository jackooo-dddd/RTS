From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.
Require Export prosa.util.notation.
Require Export prosa.util.rel.
Require Export prosa.util.nat.

Module Generated_util__sum.

Section ExtractedContext_0.
  Variable (I : eqType).
  Variable (r : seq I).
  Variable (P : pred I).
    Variable (F : I -> nat).

    Lemma sum_nat_eq0_nat :
      (\sum_(i <- r | P i) F i == 0) = all (fun x => F x == 0) [seq x <- r | P x].
    Proof.
      elim: r => [|x r' IH]; rewrite ?big_nil//= big_cons.
      by case: ifP; rewrite ?addn_eq0 IH.
    Qed.

End ExtractedContext_0.

Lemma sum_of_ones :
  forall t Δ,
    \sum_(t <= x < t + Δ) 1 = Δ.
Proof. by move=> t Δ; rewrite big_const_nat iter_addn_0 mul1n addKn. Qed.

Lemma big_nat_eq0 m n F :
  \sum_(m <= i < n) F i = 0 <-> (forall i, m <= i < n -> F i = 0).
Proof.
  split.
  - rewrite /index_iota => /eqP.
    rewrite sum_nat_eq0_nat filter_predT => /allP ZERO i.
    rewrite -mem_index_iota /index_iota => IN.
    by apply/eqP; apply ZERO.
  - move=> ZERO.
    have-> : \sum_(m <= i < n) F i = \sum_(m <= i < n) 0 by apply eq_big_nat.
    exact: big1_eq.
Qed.

Lemma sum_le_summation_range :
  forall f t Δ,
    \sum_(t <= x < t + Δ) f x < Δ ->
    exists x, t <= x < t + Δ /\ f x = 0.
Proof.
  move=> f t; elim=> [|Δ IHΔ] H; first by rewrite ltn0 in H.
  destruct (f (t + Δ)) as [|n] eqn: EQ.
  { exists (t + Δ); split; last by done.
    by apply/andP; split; [rewrite leq_addr | rewrite addnS ltnS]. }
  { move: H; rewrite addnS big_nat_recr //= ?leq_addr // EQ addnS ltnS => H.
    have {}/IHΔ [z [/andP[LE GE] ZERO]] : \sum_(t <= t' < t + Δ) f t' < Δ.
    { by apply leq_ltn_trans with (\sum_(t <= i < t + Δ) f i + n); first rewrite leq_addr. }
    by exists z; split=> //; rewrite LE/= ltnS ltnW. }
Qed.

End Generated_util__sum.

Check @Generated_util__sum.big_nat_eq0.
Print Assumptions Generated_util__sum.big_nat_eq0.
Check @Generated_util__sum.sum_of_ones.
Print Assumptions Generated_util__sum.sum_of_ones.
Check @Generated_util__sum.sum_le_summation_range.
Print Assumptions Generated_util__sum.sum_le_summation_range.
