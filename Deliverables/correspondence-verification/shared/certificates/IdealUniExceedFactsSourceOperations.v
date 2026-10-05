From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.ideal_uni_exceed.

(** Source-side equality semantics are proved by constructor analysis of the
    official computational definition, without using the source reflection
    theorem proof constant. The cross-ITP certificate composes this fact with
    the actual imported Lean equality observer. *)
Lemma exceedance_source_eqdef_iff (Job : eqType)
    (x y : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job) :
  is_true
    (@prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef
      Job x y) <-> Logic.eq x y.
Proof.
  destruct x as [a|a|]; destruct y as [b|b|]; cbn;
    try (split; [intro H; discriminate H | intro H; discriminate H]);
    split.
  - move/eqP=> H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
  - move/eqP=> H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
  - intro H. reflexivity.
  - intro H. reflexivity.
Qed.

Print Assumptions exceedance_source_eqdef_iff.
