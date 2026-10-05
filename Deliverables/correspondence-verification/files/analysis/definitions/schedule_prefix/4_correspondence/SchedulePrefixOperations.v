From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.definitions.schedule_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSchedulePrefix ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ServiceBaseAdapter.

(** Minimal artifact-local replay of the already certified finite Boolean
    existential construction from ServiceScheduleOperations.v.  The
    constructors belong to this exact imported Lean artifact. *)
Inductive PrefixSourceTrue : SProp := prefix_source_true_intro.
Inductive PrefixSourceFalse : SProp := .

Definition PrefixSourceBoolTruth (b : bool) : SProp :=
  match b with true => PrefixSourceTrue | false => PrefixSourceFalse end.

Definition prefix_source_false_elim (Q : SProp)
    (H : PrefixSourceFalse) : Q := match H return Q with end.

Definition prefix_coq_false_ne_true (H : Logic.eq false true) :
    PrefixSourceFalse :=
  match H in Logic.eq _ z return
    match z with true => PrefixSourceFalse | false => PrefixSourceTrue end
  with Logic.eq_refl => prefix_source_true_intro end.

Definition prefix_prop_to_source_truth (b : bool) :
    is_true b -> PrefixSourceBoolTruth b :=
  match b return is_true b -> PrefixSourceBoolTruth b with
  | true => fun _ => prefix_source_true_intro
  | false => fun H => prefix_source_false_elim _
      (prefix_coq_false_ne_true H)
  end.

Definition prefix_bool_true_elim (bR : bool)
    (bL : ImportedSchedulePrefix.Bool) :
  SvcBoolRel bR bL ->
  Lean.eq bL ImportedSchedulePrefix.Bool_true ->
  PrefixSourceBoolTruth bR.
Proof.
  destruct bR, bL; cbn; intros Hrel Htrue.
  - exact prefix_source_true_intro.
  - exact prefix_source_true_intro.
  - exact (svc_false_elim _ (svc_false_ne_true Htrue)).
  - exact (svc_false_elim _ (svc_false_ne_true Hrel)).
Defined.

Definition prefix_exists_intro_strict (T : finType) (p : pred T)
    (x : T) :
  PrefixSourceBoolTruth (p x) ->
  StrictlyInhabited (is_true [exists y : T, p y]).
Proof.
  destruct (p x) eqn:Hpx.
  - intro Htruth. apply strictly_inhabits. apply/existsP.
    exists x. exact Hpx.
  - exact (prefix_source_false_elim _).
Defined.

Lemma prefix_mathcomp_exists_as_has_enum (T : finType) (p : pred T) :
  [exists x : T, p x] = has p (enum T).
Proof.
  apply/idP/idP.
  - move/existsP=> [x Hx]. apply/hasP.
    exists x; first exact: mem_enum. exact Hx.
  - move/hasP=> [x _ Hx]. apply/existsP.
    exists x. exact Hx.
Qed.

Fixpoint prefix_exists_forward_seq
    (CoreR CoreL : Type) (toL : CoreR -> CoreL)
    (pR : CoreR -> bool) (pL : CoreL -> ImportedSchedulePrefix.Bool)
    (Hpred : forall cR, SvcBoolRel (pR cR) (pL (toL cR)))
    (xs : seq CoreR) :
  PrefixSourceBoolTruth (has pR xs) ->
  ImportedSchedulePrefix.Exists CoreL
    (fun cL => Lean.eq (pL cL) ImportedSchedulePrefix.Bool_true) :=
  match xs as ys return
    PrefixSourceBoolTruth (has pR ys) ->
    ImportedSchedulePrefix.Exists CoreL
      (fun cL => Lean.eq (pL cL) ImportedSchedulePrefix.Bool_true)
  with
  | [::] => prefix_source_false_elim _
  | cR :: tail =>
      match pR cR as b return
        SvcBoolRel b (pL (toL cR)) ->
        PrefixSourceBoolTruth (b || has pR tail) ->
        ImportedSchedulePrefix.Exists CoreL
          (fun cL => Lean.eq (pL cL) ImportedSchedulePrefix.Bool_true)
      with
      | true => fun Hrel _ =>
          ImportedSchedulePrefix.Exists_intro _ _ (toL cR)
            (sub_imported_eq_sym _ _ Hrel)
      | false => fun _ Htail =>
          prefix_exists_forward_seq CoreR CoreL toL pR pL Hpred tail Htail
      end (Hpred cR)
  end.

(** Only the state/core observations required by prefix equality and
    scheduled-at.  These are representation data, not an assumed
    correspondence for either target declaration. *)
Section PrefixRepresentation.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState_State
      Job (svc_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState_Core
      Job (svc_decidable_eq Job) PStateL.

  Record PrefixProcessorRel : Type := {
    prefix_state_to_target : StateR -> StateL;
    prefix_state_to_source : StateL -> StateR;
    prefix_state_source_roundtrip : forall sR,
      Logic.eq (prefix_state_to_source (prefix_state_to_target sR)) sR;
    prefix_state_target_roundtrip : forall sL,
      Lean.eq (prefix_state_to_target (prefix_state_to_source sL)) sL;
    prefix_core_to_target : CoreR -> CoreL;
    prefix_core_to_source : CoreL -> CoreR;
    prefix_core_target_roundtrip : forall cL,
      Lean.eq (prefix_core_to_target (prefix_core_to_source cL)) cL;
    prefix_scheduled_on_related : forall j sR cR,
      SvcBoolRel
        (@prosa.behavior.schedule.scheduled_on Job PStateR j sR cR)
        (ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
          Job (svc_decidable_eq Job) PStateL j
          (prefix_state_to_target sR) (prefix_core_to_target cR))
  }.

  Variable R : PrefixProcessorRel.

  Definition PrefixScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL) : SProp :=
    forall tL : Lean.Nat,
      Lean.eq
        (prefix_state_to_target R (schedR (sub_nat_to_rocq tL)))
        (schedL tL).

  Definition prefix_schedule_to_target
      (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL :=
    fun tL => prefix_state_to_target R (schedR (sub_nat_to_rocq tL)).

  Lemma prefix_schedule_canonical schedR :
    PrefixScheduleRel schedR (prefix_schedule_to_target schedR).
  Proof. intro tL. exact (@Lean.eq_refl _ _). Qed.

  Lemma prefix_schedule_at_related schedR schedL (tR : nat)
      (tL : Lean.Nat) :
    PrefixScheduleRel schedR schedL ->
    SubNatRel tR tL ->
    Lean.eq (prefix_state_to_target R (schedR tR)) (schedL tL).
  Proof.
    intros Hsched Ht. destruct Ht.
    have H := Hsched (sub_nat_to_imported tR).
    rewrite (sub_nat_rocq_roundtrip tR) in H.
    exact H.
  Qed.

  Lemma identical_prefix_correspondence
      (schedR schedR' : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL schedL' : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL)
      (hR : nat) (hL : Lean.Nat) :
    PrefixScheduleRel schedR schedL ->
    PrefixScheduleRel schedR' schedL' ->
    SubNatRel hR hL ->
    PropSPropRel
      (@prosa.analysis.definitions.schedule_prefix.identical_prefix
        Job PStateR schedR schedR' hR)
      (ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
        Job (svc_decidable_eq Job) PStateL schedL schedL' hL).
  Proof.
    intros Hsched Hsched' Hh.
    unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
    cbn [ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix].
    apply prop_sprop_rel_intro.
    - intros Hprefix tL HltL.
      pose (tR := sub_nat_to_rocq tL).
      have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
      have HltR := sprop_to_prop _ _
        (sub_nat_lt_correspondence tR tL hR hL Ht Hh) HltL.
      have Hstates := Hprefix tR HltR.
      have E1 := prefix_schedule_at_related
        schedR schedL tR tL Hsched Ht.
      have E2 := prefix_schedule_at_related
        schedR' schedL' tR tL Hsched' Ht.
      exact (sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _ E1)
        (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _
            (f_equal (prefix_state_to_target R) Hstates)) E2)).
    - intro HprefixL. apply strictly_inhabits.
      intros tR HltR.
      pose (tL := sub_nat_to_imported tR).
      have Ht : SubNatRel tR tL := sub_nat_rel_canonical tR.
      have HltL := prop_to_sprop _ _
        (sub_nat_lt_correspondence tR tL hR hL Ht Hh) HltR.
      have Hstates := HprefixL tL HltL.
      have E1 := prefix_schedule_at_related
        schedR schedL tR tL Hsched Ht.
      have E2 := prefix_schedule_at_related
        schedR' schedL' tR tL Hsched' Ht.
      have Hmapped : Lean.eq
          (prefix_state_to_target R (schedR tR))
          (prefix_state_to_target R (schedR' tR)) :=
        sub_imported_eq_trans _ _ _ E1
          (sub_imported_eq_trans _ _ _ Hstates
            (sub_imported_eq_sym _ _ E2)).
      have Hsource := f_equal (prefix_state_to_source R)
        (imported_eq_to_coq_eq _ _ Hmapped).
      rewrite (prefix_state_source_roundtrip R (schedR tR)) in Hsource.
      rewrite (prefix_state_source_roundtrip R (schedR' tR)) in Hsource.
      exact Hsource.
  Qed.

  Lemma identical_prefix_inclusion_statement_correspondence
      (schedR schedR' : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL schedL' : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL)
      (hR hR' : nat) (hL hL' : Lean.Nat) :
    PrefixScheduleRel schedR schedL ->
    PrefixScheduleRel schedR' schedL' ->
    SubNatRel hR hL -> SubNatRel hR' hL' ->
    PropSPropRel
      ((hR' <= hR)%N ->
       @prosa.analysis.definitions.schedule_prefix.identical_prefix
         Job PStateR schedR schedR' hR ->
       @prosa.analysis.definitions.schedule_prefix.identical_prefix
         Job PStateR schedR schedR' hR')
      (ImportedSchedulePrefix.LE_le_inst1 Lean.Nat
        ImportedSchedulePrefix.instLENat hL' hL ->
       ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
         Job (svc_decidable_eq Job) PStateL schedL schedL' hL ->
       ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
         Job (svc_decidable_eq Job) PStateL schedL schedL' hL').
  Proof.
    intros Hsched Hsched' Hh Hh'.
    have Hle := sub_nat_le_correspondence hR' hL' hR hL Hh' Hh.
    have Hprefix := identical_prefix_correspondence
      schedR schedR' schedL schedL' hR hL Hsched Hsched' Hh.
    have Hprefix' := identical_prefix_correspondence
      schedR schedR' schedL schedL' hR' hL' Hsched Hsched' Hh'.
    apply prop_sprop_rel_intro.
    - intros Hsource HleL HprefixL.
      apply (prop_to_sprop _ _ Hprefix').
      exact (Hsource (sprop_to_prop _ _ Hle HleL)
        (sprop_to_prop _ _ Hprefix HprefixL)).
    - intro Htarget. apply strictly_inhabits.
      intros HleR HprefixR.
      apply (sprop_to_prop _ _ Hprefix').
      exact (Htarget (prop_to_sprop _ _ Hle HleR)
        (prop_to_sprop _ _ Hprefix HprefixR)).
  Qed.

  Definition prefix_target_scheduled_on (j : Job) (s : StateL)
      (c : CoreL) : ImportedSchedulePrefix.Bool :=
    ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
      Job (svc_decidable_eq Job) PStateL j s c.

  Lemma prefix_scheduled_on_at (j : Job) (sR : StateR)
      (sL : StateL) (cR : CoreR) :
    Lean.eq (prefix_state_to_target R sR) sL ->
    SvcBoolRel
      (@prosa.behavior.schedule.scheduled_on Job PStateR j sR cR)
      (prefix_target_scheduled_on j sL (prefix_core_to_target R cR)).
  Proof.
    intro Hstate. unfold SvcBoolRel.
    exact (sub_imported_eq_trans _ _ _
      (prefix_scheduled_on_related R j sR cR)
      (sub_imported_eq_congr
        (fun s => prefix_target_scheduled_on j s (prefix_core_to_target R cR))
        _ _ Hstate)).
  Qed.

  Lemma prefix_bool_rel_from_truth (bR : bool)
      (bL : ImportedSchedulePrefix.Bool) :
    (is_true bR -> Lean.eq bL ImportedSchedulePrefix.Bool_true) ->
    (Lean.eq bL ImportedSchedulePrefix.Bool_true ->
       StrictlyInhabited (is_true bR)) ->
    SvcBoolRel bR bL.
  Proof.
    destruct bR, bL; cbn; intros Hforward Hbackward.
    - exact (svc_false_elim _
        (svc_false_ne_true (Hforward (Logic.eq_refl true)))).
    - exact (@Lean.eq_refl _ _).
    - exact (@Lean.eq_refl _ _).
    - destruct (Hbackward (@Lean.eq_refl _ _)) as [Hfalse].
      discriminate Hfalse.
  Qed.

  Lemma prefix_scheduled_in_related (j : Job) (sR : StateR)
      (sL : StateL) :
    Lean.eq (prefix_state_to_target R sR) sL ->
    SvcBoolRel
      (@prosa.behavior.schedule.scheduled_in Job PStateR j sR)
      (ImportedSchedulePrefix.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
        Job (svc_decidable_eq Job) PStateL j sL).
  Proof.
    intro Hstate. apply prefix_bool_rel_from_truth.
    - intro Hsource.
      have Htruth := prefix_prop_to_source_truth _ Hsource.
      unfold prosa.behavior.schedule.scheduled_in in Htruth.
      rewrite prefix_mathcomp_exists_as_has_enum in Htruth.
      apply (ImportedSchedulePrefix.mpr _ _
        (ImportedSchedulePrefix.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (svc_decidable_eq Job) PStateL j sL)).
      exact (prefix_exists_forward_seq CoreR CoreL
        (prefix_core_to_target R)
        [eta @prosa.behavior.schedule.scheduled_on Job PStateR j sR]
        (prefix_target_scheduled_on j sL)
        (fun cR => prefix_scheduled_on_at j sR sL cR Hstate)
        (enum CoreR) Htruth).
    - intro Htarget.
      have Hexists := ImportedSchedulePrefix.mp _ _
        (ImportedSchedulePrefix.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (svc_decidable_eq Job) PStateL j sL) Htarget.
      destruct Hexists as [cL HcL].
      apply (prefix_exists_intro_strict CoreR
        [eta @prosa.behavior.schedule.scheduled_on Job PStateR j sR]
        (prefix_core_to_source R cL)).
      have Hrel := prefix_scheduled_on_at j sR sL
        (prefix_core_to_source R cL) Hstate.
      have Hcore := sub_imported_eq_congr
        (prefix_target_scheduled_on j sL) _ _
        (prefix_core_target_roundtrip R cL).
      exact (prefix_bool_true_elim _ _
        (sub_imported_eq_trans _ _ _ Hrel Hcore) HcL).
  Qed.

  Lemma prefix_scheduled_at_related
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    PrefixScheduleRel schedR schedL ->
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (ImportedSchedulePrefix.Prosa_Behavior_Service_scheduled_at
        Job (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.behavior.service.scheduled_at.
    cbn [ImportedSchedulePrefix.Prosa_Behavior_Service_scheduled_at].
    exact (prefix_scheduled_in_related j (schedR tR) (schedL tL)
      (prefix_schedule_at_related schedR schedL tR tL Hsched Ht)).
  Qed.

  Lemma prefix_bool_equality_correspondence
      (bR bR' : bool)
      (bL bL' : ImportedSchedulePrefix.Bool) :
    SvcBoolRel bR bL -> SvcBoolRel bR' bL' ->
    PropSPropRel (Logic.eq bR bR') (Lean.eq bL bL').
  Proof.
    intros Hb Hb'. apply prop_sprop_rel_intro.
    - intro Heq. destruct Heq.
      exact (sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _ Hb) Hb').
    - intro Htarget. apply strictly_inhabits.
      have Hcanon : Lean.eq (svc_bool_to_imported bR)
          (svc_bool_to_imported bR') :=
        sub_imported_eq_trans _ _ _ Hb
          (sub_imported_eq_trans _ _ _ Htarget
            (sub_imported_eq_sym _ _ Hb')).
      have Hsource := f_equal svc_bool_to_rocq
        (imported_eq_to_coq_eq _ _ Hcanon).
      rewrite (svc_bool_source_roundtrip bR) in Hsource.
      rewrite (svc_bool_source_roundtrip bR') in Hsource.
      exact Hsource.
  Qed.

  Lemma identical_prefix_scheduled_at_statement_correspondence
      (schedR schedR' : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL schedL' : ImportedSchedulePrefix.Prosa_Behavior_Schedule_schedule
        Job (svc_decidable_eq Job) PStateL)
      (hR tR : nat) (hL tL : Lean.Nat) (j : Job) :
    PrefixScheduleRel schedR schedL ->
    PrefixScheduleRel schedR' schedL' ->
    SubNatRel hR hL -> SubNatRel tR tL ->
    PropSPropRel
      (@prosa.analysis.definitions.schedule_prefix.identical_prefix
          Job PStateR schedR schedR' hR ->
       (tR < hR)%N ->
       Logic.eq
         (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
         (@prosa.behavior.service.scheduled_at Job PStateR schedR' j tR))
      (ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
          Job (svc_decidable_eq Job) PStateL schedL schedL' hL ->
       ImportedSchedulePrefix.LT_lt_inst1 Lean.Nat
          ImportedSchedulePrefix.instLTNat tL hL ->
       Lean.eq
         (ImportedSchedulePrefix.Prosa_Behavior_Service_scheduled_at
           Job (svc_decidable_eq Job) PStateL schedL j tL)
         (ImportedSchedulePrefix.Prosa_Behavior_Service_scheduled_at
           Job (svc_decidable_eq Job) PStateL schedL' j tL)).
  Proof.
    intros Hsched Hsched' Hh Ht.
    have Hprefix := identical_prefix_correspondence
      schedR schedR' schedL schedL' hR hL Hsched Hsched' Hh.
    have Hlt := sub_nat_lt_correspondence tR tL hR hL Ht Hh.
    have Hleft := prefix_scheduled_at_related
      schedR schedL j tR tL Hsched Ht.
    have Hright := prefix_scheduled_at_related
      schedR' schedL' j tR tL Hsched' Ht.
    have Heq := prefix_bool_equality_correspondence _ _ _ _
      Hleft Hright.
    apply prop_sprop_rel_intro.
    - intros Hsource HprefixL HltL.
      apply (prop_to_sprop _ _ Heq).
      exact (Hsource (sprop_to_prop _ _ Hprefix HprefixL)
        (sprop_to_prop _ _ Hlt HltL)).
    - intro Htarget. apply strictly_inhabits.
      intros HprefixR HltR.
      apply (sprop_to_prop _ _ Heq).
      exact (Htarget (prop_to_sprop _ _ Hprefix HprefixR)
        (prop_to_sprop _ _ Hlt HltR)).
  Qed.
End PrefixRepresentation.
