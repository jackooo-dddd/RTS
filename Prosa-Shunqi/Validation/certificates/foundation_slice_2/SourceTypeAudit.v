From prosa Require Import
  util.notation util.tactics util.rel util.seqset util.subadditivity util.supremum.
From FoundationImported Require Import ImportedTactics.

(** Kernel guards tying the independently proved logical relation to the exact
    elaborated source and imported target theorem types.  These guards use the
    theorem proof constants only for type checking; semantic certificates do
    not depend on either guard or proof constant. *)
Definition rocq_modusponens_type_guard :
  forall P Q : Prop, P -> (P -> Q) -> Q :=
  @prosa.util.tactics.modusponens.

Definition imported_modusponens_type_guard :
  forall P Q : SProp, P -> (P -> Q) -> Q :=
  @Prosa_Util_Tactics_modusponens.

Check @prosa.util.notation.constant.
Check @prosa.util.tactics.neqP.
Check @prosa.util.tactics.modusponens.
Check @prosa.util.rel.monotone.
Check @prosa.util.rel.total_over_list.
Check @prosa.util.rel.antisymmetric_over_list.
Check @prosa.util.seqset.set.
Check @prosa.util.seqset.set_of.
Check @prosa.util.seqset.set_uniq.
Check @prosa.util.subadditivity.subadditive_at.
Check @prosa.util.subadditivity.subadditive_until.
Check @prosa.util.subadditivity.subadditive.
Check @prosa.util.subadditivity.subadditive_standard.
Check @prosa.util.subadditivity.subadditive_standard_equivalence.
Check @prosa.util.subadditivity.subadditive_leq_mul.
Check @prosa.util.supremum.choose_superior.
Check @prosa.util.supremum.supremum.
Check @prosa.util.supremum.supremum_unfold.
Check @prosa.util.supremum.supremum_exists.
Check @prosa.util.supremum.supremum_none.
Check @prosa.util.supremum.supremum_in.
Check @prosa.util.supremum.supremum_spec.
