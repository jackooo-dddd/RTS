From mathcomp Require Import ssreflect ssrbool ssrnat.
Require Import Relations.

Lemma nat_rel_refl n : NatRel n n.
Proof. by []. Qed.

Lemma nat_le_bridge nR nL mR mL :
  NatRel nR nL -> NatRel mR mL -> (nR <= mR) = (nL <= mL).
Proof. by move=> -> ->. Qed.

Lemma nat_ge_bool_prop_bridge serviceR serviceL costR costL :
  NatRel serviceR serviceL -> NatRel costR costL ->
  BoolPropRel (costR <= serviceR) (costL <= serviceL)%coq_nat.
Proof.
  move=> -> ->; split.
  - by move/leP.
  - by move=> H; apply/leP.
Qed.
