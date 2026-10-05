From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSupremum.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SupremumCertificate
  SupremumTheoremCorrespondence.
From prosa Require Import util.supremum.

Definition SupPointwise (T : Type) (RR : T -> T -> bool)
    (RL : T -> T -> ImportedSupremum.Bool) : SProp :=
  forall x y, SupBoolRel (RR x y) (RL x y).

(** Exact theorem-type guards.  These are provenance checks and are kept
    separate from the semantic certificates below. *)
Definition rocq_supremum_unfold_type_guard (T : eqType) (R : rel T) :
  forall head tail,
    @prosa.util.supremum.supremum T R (head :: tail) =
    @prosa.util.supremum.choose_superior T R head
      (@prosa.util.supremum.supremum T R tail) :=
  @prosa.util.supremum.supremum_unfold T R.

Definition imported_supremum_unfold_type_guard (T : eqType)
    (R : T -> T -> ImportedSupremum.Bool) :
  forall head tail,
    Lean.eq
      (Prosa_Util_Supremum_supremum T R
        (ImportedSupremum.List_cons T head tail))
      (Prosa_Util_Supremum_choose_superior T R head
        (Prosa_Util_Supremum_supremum T R tail)) :=
  Prosa_Util_Supremum_supremum_unfold T
    (sup_eqtype_decidable_eq T) R.

Lemma supremum_unfold_statement_correspondence_certificate :
  forall (T : eqType) (RR : T -> T -> bool)
         (RL : T -> T -> ImportedSupremum.Bool),
    SupPointwise T RR RL ->
    forall head tailR tailL,
      SupListRel T tailR tailL ->
      PropSPropRel
        (@prosa.util.supremum.supremum T RR (head :: tailR) =
         @prosa.util.supremum.choose_superior T RR head
           (@prosa.util.supremum.supremum T RR tailR))
        (Lean.eq
          (Prosa_Util_Supremum_supremum T RL
            (ImportedSupremum.List_cons T head tailL))
          (Prosa_Util_Supremum_choose_superior T RL head
            (Prosa_Util_Supremum_supremum T RL tailL))).
Proof.
  intros T RR RL HR head tailR tailL Htail.
  apply sup_option_eq_correspondence.
  - exact (supremum_correspondence_certificate T RR RL HR _ _
      (sup_list_cons T head tailR tailL Htail)).
  - exact (choose_superior_correspondence_certificate T RR RL HR head _ _
      (supremum_correspondence_certificate T RR RL HR _ _ Htail)).
Qed.

Definition rocq_supremum_exists_type_guard (T : eqType) (R : rel T) :
  forall (x : T) (s : seq T),
    x \in s -> @prosa.util.supremum.supremum T R s != None :=
  @prosa.util.supremum.supremum_exists T R.

Definition imported_supremum_exists_type_guard (T : eqType)
    (R : T -> T -> ImportedSupremum.Bool) :
  forall (x : T) (s : ImportedSupremum.List T),
    sup_imported_mem T x s ->
    ImportedSupremum.Ne (ImportedSupremum.Option T)
      (Prosa_Util_Supremum_supremum T R s)
      (ImportedSupremum.Option_none T) :=
  Prosa_Util_Supremum_supremum_exists T
    (sup_eqtype_decidable_eq T) R.

Lemma supremum_exists_statement_correspondence_certificate :
  forall (T : eqType) (RR : T -> T -> bool)
         (RL : T -> T -> ImportedSupremum.Bool),
    SupPointwise T RR RL ->
    forall x sR sL, SupListRel T sR sL ->
    PropSPropRel
      (x \in sR -> @prosa.util.supremum.supremum T RR sR != None)
      (sup_imported_mem T x sL ->
       ImportedSupremum.Ne (ImportedSupremum.Option T)
         (Prosa_Util_Supremum_supremum T RL sL)
         (ImportedSupremum.Option_none T)).
Proof.
  intros T RR RL HR x sR sL Hs. apply prop_sprop_rel_intro.
  - intros Hsource HmemL.
    have HmemR := sprop_to_prop _ _
      (sup_membership_correspondence T x sR sL Hs) HmemL.
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    exact (prop_to_sprop _ _
      (sup_option_ne_correspondence T _ _ _ _ Hsup (sup_option_none T))
      (Hsource HmemR)).
  - intro Htarget. apply strictly_inhabits. intro HmemR.
    have HmemL := prop_to_sprop _ _
      (sup_membership_correspondence T x sR sL Hs) HmemR.
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    exact (sprop_to_prop _ _
      (sup_option_ne_correspondence T _ _ _ _ Hsup (sup_option_none T))
      (Htarget HmemL)).
Qed.

Definition rocq_supremum_none_type_guard (T : eqType) (R : rel T) :
  forall s : seq T,
    @prosa.util.supremum.supremum T R s = None -> s = [::] :=
  @prosa.util.supremum.supremum_none T R.

Definition imported_supremum_none_type_guard (T : eqType)
    (R : T -> T -> ImportedSupremum.Bool) :
  forall s : ImportedSupremum.List T,
    Lean.eq (Prosa_Util_Supremum_supremum T R s)
      (ImportedSupremum.Option_none T) ->
    Lean.eq s (ImportedSupremum.List_nil T) :=
  Prosa_Util_Supremum_supremum_none T
    (sup_eqtype_decidable_eq T) R.

Lemma supremum_none_statement_correspondence_certificate :
  forall (T : eqType) (RR : T -> T -> bool)
         (RL : T -> T -> ImportedSupremum.Bool),
    SupPointwise T RR RL ->
    forall sR sL, SupListRel T sR sL ->
    PropSPropRel
      (@prosa.util.supremum.supremum T RR sR = None -> sR = [::])
      (Lean.eq (Prosa_Util_Supremum_supremum T RL sL)
          (ImportedSupremum.Option_none T) ->
       Lean.eq sL (ImportedSupremum.List_nil T)).
Proof.
  intros T RR RL HR sR sL Hs. apply prop_sprop_rel_intro.
  - intros Hsource HnoneL.
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    have HnoneR := sprop_to_prop _ _
      (sup_option_eq_correspondence T _ _ _ _ Hsup (sup_option_none T))
      HnoneL.
    exact (prop_to_sprop _ _
      (sup_list_eq_correspondence T sR [::] sL
        (ImportedSupremum.List_nil T) Hs (sup_list_nil T))
      (Hsource HnoneR)).
  - intro Htarget. apply strictly_inhabits. intro HnoneR.
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    have HnoneL := prop_to_sprop _ _
      (sup_option_eq_correspondence T _ _ _ _ Hsup (sup_option_none T))
      HnoneR.
    exact (sprop_to_prop _ _
      (sup_list_eq_correspondence T sR [::] sL
        (ImportedSupremum.List_nil T) Hs (sup_list_nil T))
      (Htarget HnoneL)).
Qed.

Definition rocq_supremum_in_type_guard (T : eqType) (R : rel T) :
  forall (x : T) (s : seq T),
    @prosa.util.supremum.supremum T R s = Some x -> x \in s :=
  @prosa.util.supremum.supremum_in T R.

Definition imported_supremum_in_type_guard (T : eqType)
    (R : T -> T -> ImportedSupremum.Bool) :
  forall (x : T) (s : ImportedSupremum.List T),
    Lean.eq (Prosa_Util_Supremum_supremum T R s)
      (ImportedSupremum.Option_some T x) ->
    sup_imported_mem T x s :=
  Prosa_Util_Supremum_supremum_in T
    (sup_eqtype_decidable_eq T) R.

Lemma supremum_in_statement_correspondence_certificate :
  forall (T : eqType) (RR : T -> T -> bool)
         (RL : T -> T -> ImportedSupremum.Bool),
    SupPointwise T RR RL ->
    forall x sR sL, SupListRel T sR sL ->
    PropSPropRel
      (@prosa.util.supremum.supremum T RR sR = Some x -> x \in sR)
      (Lean.eq (Prosa_Util_Supremum_supremum T RL sL)
          (ImportedSupremum.Option_some T x) ->
       sup_imported_mem T x sL).
Proof.
  intros T RR RL HR x sR sL Hs. apply prop_sprop_rel_intro.
  - intros Hsource HsomeL.
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    have HsomeR := sprop_to_prop _ _
      (sup_option_eq_correspondence T _ _ _ _ Hsup (sup_option_some T x))
      HsomeL.
    exact (prop_to_sprop _ _
      (sup_membership_correspondence T x sR sL Hs)
      (Hsource HsomeR)).
  - intro Htarget. apply strictly_inhabits. intro HsomeR.
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    have HsomeL := prop_to_sprop _ _
      (sup_option_eq_correspondence T _ _ _ _ Hsup (sup_option_some T x))
      HsomeR.
    exact (sprop_to_prop _ _
      (sup_membership_correspondence T x sR sL Hs)
      (Htarget HsomeL)).
Qed.

Definition SupSourceReflexive (T : eqType) (R : T -> T -> bool) : Prop :=
  forall x, is_true (R x x).

Definition SupTargetReflexive (T : Type)
    (R : T -> T -> ImportedSupremum.Bool) : SProp :=
  forall x, Lean.eq (R x x) ImportedSupremum.Bool_true.

Definition SupSourceTotal (T : eqType) (R : T -> T -> bool) : Prop :=
  forall x y, is_true (R x y || R y x).

Definition SupTargetTotal (T : Type)
    (R : T -> T -> ImportedSupremum.Bool) : SProp :=
  forall x y,
    Lean.eq (ImportedSupremum.Bool_or (R x y) (R y x))
      ImportedSupremum.Bool_true.

Definition SupSourceTransitive (T : eqType) (R : T -> T -> bool) : Prop :=
  forall y x z, is_true (R x y) -> is_true (R y z) -> is_true (R x z).

Definition SupTargetTransitive (T : Type)
    (R : T -> T -> ImportedSupremum.Bool) : SProp :=
  forall x y z,
    Lean.eq (R x y) ImportedSupremum.Bool_true ->
    Lean.eq (R y z) ImportedSupremum.Bool_true ->
    Lean.eq (R x z) ImportedSupremum.Bool_true.

Definition SupSourceSpecStatement (T : eqType) (R : T -> T -> bool) : Prop :=
  SupSourceReflexive T R ->
  SupSourceTotal T R ->
  SupSourceTransitive T R ->
  forall (x : T) (s : seq T),
    @prosa.util.supremum.supremum T R s = Some x ->
    forall y, y \in s -> is_true (R x y).

Definition SupTargetSpecStatement (T : Type)
    (R : T -> T -> ImportedSupremum.Bool) : SProp :=
  SupTargetReflexive T R ->
  SupTargetTotal T R ->
  SupTargetTransitive T R ->
  forall (x : T) (s : ImportedSupremum.List T),
    Lean.eq (Prosa_Util_Supremum_supremum T R s)
      (ImportedSupremum.Option_some T x) ->
    forall y, sup_imported_mem T y s ->
      Lean.eq (R x y) ImportedSupremum.Bool_true.

Definition rocq_supremum_spec_type_guard (T : eqType) (R : rel T) :
  SupSourceSpecStatement T R := @prosa.util.supremum.supremum_spec T R.

Definition imported_supremum_spec_type_guard (T : eqType)
    (R : T -> T -> ImportedSupremum.Bool) :
  SupTargetSpecStatement T R :=
  Prosa_Util_Supremum_supremum_spec T
    (sup_eqtype_decidable_eq T) R.

Lemma supremum_spec_statement_correspondence_certificate :
  forall (T : eqType) (RR : T -> T -> bool)
         (RL : T -> T -> ImportedSupremum.Bool),
    SupPointwise T RR RL ->
    PropSPropRel (SupSourceSpecStatement T RR)
      (SupTargetSpecStatement T RL).
Proof.
  intros T RR RL HR. apply prop_sprop_rel_intro.
  - intros Hsource HreflL HtotalL HtransL x sL HsomeL y HmemL.
    set (sR := sup_imported_to_seq sL).
    have Hs : SupListRel T sR sL := sup_list_rel_surjective sL.
    have HreflR : SupSourceReflexive T RR := fun a =>
      sprop_to_prop _ _ (sup_bool_true_correspondence _ _ (HR a a))
        (HreflL a).
    have HtotalR : SupSourceTotal T RR := fun a b =>
      sprop_to_prop _ _
        (sup_bool_true_correspondence _ _
          (sup_bool_or_correspondence _ _ _ _ (HR a b) (HR b a)))
        (HtotalL a b).
    have HtransR : SupSourceTransitive T RR := fun y0 x0 z0 HxyR HyzR =>
      sprop_to_prop _ _ (sup_bool_true_correspondence _ _ (HR x0 z0))
        (HtransL x0 y0 z0
          (prop_to_sprop _ _
            (sup_bool_true_correspondence _ _ (HR x0 y0)) HxyR)
          (prop_to_sprop _ _
            (sup_bool_true_correspondence _ _ (HR y0 z0)) HyzR)).
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    have HsomeR := sprop_to_prop _ _
      (sup_option_eq_correspondence T _ _ _ _ Hsup (sup_option_some T x))
      HsomeL.
    have HmemR := sprop_to_prop _ _
      (sup_membership_correspondence T y sR sL Hs) HmemL.
    exact (prop_to_sprop _ _
      (sup_bool_true_correspondence _ _ (HR x y))
      (Hsource HreflR HtotalR HtransR x sR HsomeR y HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros HreflR HtotalR HtransR x sR HsomeR y HmemR.
    set (sL := sup_seq_to_imported sR).
    have Hs : SupListRel T sR sL := sup_list_rel_canonical sR.
    have HreflL : SupTargetReflexive T RL := fun a =>
      prop_to_sprop _ _ (sup_bool_true_correspondence _ _ (HR a a))
        (HreflR a).
    have HtotalL : SupTargetTotal T RL := fun a b =>
      prop_to_sprop _ _
        (sup_bool_true_correspondence _ _
          (sup_bool_or_correspondence _ _ _ _ (HR a b) (HR b a)))
        (HtotalR a b).
    have HtransL : SupTargetTransitive T RL := fun x0 y0 z0 HxyL HyzL =>
      prop_to_sprop _ _ (sup_bool_true_correspondence _ _ (HR x0 z0))
        (HtransR y0 x0 z0
          (sprop_to_prop _ _
            (sup_bool_true_correspondence _ _ (HR x0 y0)) HxyL)
          (sprop_to_prop _ _
            (sup_bool_true_correspondence _ _ (HR y0 z0)) HyzL)).
    have Hsup := supremum_correspondence_certificate T RR RL HR _ _ Hs.
    have HsomeL := prop_to_sprop _ _
      (sup_option_eq_correspondence T _ _ _ _ Hsup (sup_option_some T x))
      HsomeR.
    have HmemL := prop_to_sprop _ _
      (sup_membership_correspondence T y sR sL Hs) HmemR.
    exact (sprop_to_prop _ _
      (sup_bool_true_correspondence _ _ (HR x y))
      (Htarget HreflL HtotalL HtransL x sL HsomeL y HmemL)).
Qed.

Print Assumptions supremum_unfold_statement_correspondence_certificate.
Print Assumptions supremum_exists_statement_correspondence_certificate.
Print Assumptions supremum_none_statement_correspondence_certificate.
Print Assumptions supremum_in_statement_correspondence_certificate.
Print Assumptions supremum_spec_statement_correspondence_certificate.
