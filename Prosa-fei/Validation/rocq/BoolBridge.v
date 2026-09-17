From mathcomp Require Import ssreflect ssrbool.
Require Import Relations.

Lemma bool_rel_refl b : BoolRel b b.
Proof. by []. Qed.

Lemma bool_prop_true : BoolPropRel true True.
Proof. by split. Qed.

Lemma bool_prop_false : BoolPropRel false False.
Proof. by split. Qed.
