From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.
Require Export mathcomp.zify.zify.
Require Import prosa.util.tactics.
Require Export prosa.util.supremum.

Module Generated_util__list.

Fixpoint rem_all {X : eqType} (x : X) (xs : seq X) :=
  match xs with
  | [::] => [::]
  | a :: xs =>
    if a == x then rem_all x xs else a :: rem_all x xs
  end.

Lemma nin_rem_all :
  forall {X : eqType} (x : X) (xs : seq X),
    ~ (x \in rem_all x xs).
Proof.
  move=> X x; elim=> [//|a xs IHxs] IN.
  apply: IHxs.
  simpl in IN; destruct (a == x) eqn:EQ; first by done.
  move: IN; rewrite in_cons => /orP [/eqP EQ2 | IN]; last by done.
  by subst; exfalso; rewrite eq_refl in EQ.
Qed.

End Generated_util__list.

Check @Generated_util__list.rem_all.
Check @Generated_util__list.nin_rem_all.
Print Assumptions Generated_util__list.nin_rem_all.
