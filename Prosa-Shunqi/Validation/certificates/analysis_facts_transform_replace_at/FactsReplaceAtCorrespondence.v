From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsReplaceAtSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsReplaceAt ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsReplaceAt.
Module S := FactsReplaceAtSemanticSource.FactsReplaceAtSemanticSource.

(** Statement correspondences for [analysis/facts/transform/replace_at.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading inputs (job type, processor state, reference schedule, replacement
    time and replacement state); target side: the type of the imported Lean
    theorem at related inputs.  Processor states are related by the accepted
    two-sided [SvcProcessorStateRel]; the reference schedule and the
    replacement state are related functionally through its state conversion
    ([Lean.eq]); the replacement time by [SubNatRel].  Later binders: Nats are
    covered in both directions, jobs are identity carriers.  The replaced
    schedule is related to its target by case analysis on the replacement
    time, closed by the exported Lean case equations
    [production_replace_at_same]/[production_replace_at_other]; service and
    [scheduled_in] are the accepted Service proofs re-instantiated at this
    artifact.  No source or target statement theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fra_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma fra_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma fra_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact fra_false_correspondence.
Qed.

Lemma fra_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Qed.

Section ReplaceAt.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR := @prosa.behavior.schedule.State Job PStateR.
  Let StateL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL.
  Let toL := svc_ps_state_to_target Job PStateR PStateL R.

  (** Schedules related through the processor-state conversion. *)
  Definition FraScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL -> Lean.eq (toL (schedR tR)) (schedL tL).

  Lemma fra_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
    Lean.eq x y -> P x -> P y.
  Proof. intros H. destruct H. exact (fun p => p). Qed.

  Lemma fra_state_rel (sR : StateR) (sL : StateL) :
    Lean.eq (toL sR) sL -> svc_ps_state_rel Job PStateR PStateL R sR sL.
  Proof.
    intro H.
    exact (fra_lean_transport (fun x => svc_ps_state_rel Job PStateR PStateL R sR x)
      _ _ H (svc_ps_state_rel_canonical Job PStateR PStateL R sR)).
  Qed.

  Lemma fra_state_eq_correspondence (sR sR' : StateR) (sL sL' : StateL) :
    Lean.eq (toL sR) sL -> Lean.eq (toL sR') sL' ->
    PropSPropRel (sR = sR') (Lean.eq sL sL').
  Proof.
    intros H H'. apply prop_sprop_rel_intro.
    - intro E.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ H)
        (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (f_equal toL E)) H')).
    - intro EL. apply strictly_inhabits.
      have ET := imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ H
          (sub_imported_eq_trans _ _ _ EL (sub_imported_eq_sym _ _ H'))).
      have ES := f_equal (svc_ps_state_to_source Job PStateR PStateL R) ET.
      rewrite !(svc_ps_state_source_roundtrip Job PStateR PStateL R) in ES.
      exact ES.
  Qed.

  Section Replace.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : FraScheduleFunRel schedR schedL.
    Variable t'R : nat.
    Variable t'L : Lean.Nat.
    Hypothesis Ht' : SubNatRel t'R t'L.
    Variable nsR : StateR.
    Variable nsL : StateL.
    Hypothesis Hns : Lean.eq (toL nsR) nsL.

    Let replR := @prosa.analysis.transform.swap.replace_at Job PStateR schedR t'R nsR.
    Let replL := I.Prosa_Analysis_Transform_Swap_replace_at Job dJ PStateL schedL t'L nsL.

    Lemma fra_nat_not_eq (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL -> t'R <> tR -> I.Not (Lean.eq tL t'L).
    Proof.
      intros Ht NE. unfold I.Not. intro EL.
      refine (match NE _ return I.False with end).
      rewrite -(fra_nat_input _ _ Ht) -(fra_nat_input _ _ Ht').
      exact (Logic.eq_sym (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))).
    Qed.

    Lemma fra_src_same (tR : nat) : t'R = tR -> replR tR = nsR.
    Proof. move=> <-. by rewrite /replR /prosa.analysis.transform.swap.replace_at eqxx. Qed.

    Lemma fra_src_other (tR : nat) : t'R <> tR -> replR tR = schedR tR.
    Proof.
      move=> /eqP NE.
      by rewrite /replR /prosa.analysis.transform.swap.replace_at (negbTE NE).
    Qed.

    Lemma fra_replace_at_fun : FraScheduleFunRel replR replL.
    Proof.
      intros tR tL Ht.
      destruct (@eqP nat t'R tR) as [E|NE].
      - refine (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ (f_equal toL (fra_src_same tR E))) _).
        subst tR.
        exact (sub_imported_eq_trans _ _ _ Hns (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ReplaceAtInterface_production_replace_at_same
            Job dJ PStateL schedL t'L nsL tL
            (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ht) Ht')))).
      - refine (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ (f_equal toL (fra_src_other tR NE))) _).
        exact (sub_imported_eq_trans _ _ _ (Hsched tR tL Ht) (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ReplaceAtInterface_production_replace_at_other
            Job dJ PStateL schedL t'L nsL tL (fra_nat_not_eq tR tL Ht NE)))).
    Qed.

    Lemma fra_service_at_related schR schL (H : FraScheduleFunRel schR schL)
        (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL schL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j (schR tR) (schL tL)
        (fra_state_rel _ _ (H tR tL Ht))).
    Qed.

    Lemma fra_service_during_related schR schL (H : FraScheduleFunRel schR schL)
        (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.behavior.service.service_during Job PStateR schR j t1R t2R)
        (I.Prosa_Behavior_Service_service_during Job dJ PStateL schL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      have Hsum := svc_interval_sum_related t1R t2R t1L t2L
        (fun t => @prosa.behavior.service.service_at Job PStateR schR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schL j t)
        Ht1 Ht2 (fun tR tL Ht => fra_service_at_related schR schL H j tR tL Ht).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schR j t1R t2R)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
          Job dJ PStateL schL j t1L t2L)) in Hsum.
      exact Hsum.
    Qed.

    Lemma fra_not_scheduled_related schR schL (H : FraScheduleFunRel schR schL) (j : Job) :
      PropSPropRel (is_true (~~ @prosa.behavior.schedule.scheduled_in Job PStateR j (schR t'R)))
        (Lean.eq (I.Bool_not (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
          Job dJ PStateL j (schL t'L))) I.Bool_true).
    Proof.
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (svc_scheduled_in_related Job PStateR PStateL R j _ _ (fra_state_rel _ _ (H t'R t'L Ht'))))).
    Qed.

    Lemma fra_window_related (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      PropSPropRel (is_true (leq t1R t'R && ltn t'R t2R))
        (Lean.eq (I.Bool_and (svc_target_decide_le t1L t'L) (svc_target_decide_lt t'L t2L)) I.Bool_true).
    Proof.
      intros Ht1 Ht2.
      exact (svc_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
        (svc_decide_le_related _ _ _ _ Ht1 Ht') (svc_decide_lt_related _ _ _ _ Ht' Ht2))).
    Qed.

    Definition src_replace_at_def : Prop :=
      ltac:(body_of (fun s : S.statement_replace_at_def => s Job PStateR schedR t'R nsR)).
    Definition tgt_replace_at_def : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_replace_at_def
        Job dJ PStateL schedL t'L nsL)).
    Theorem replace_at_def_correspondence : PropSPropRel src_replace_at_def tgt_replace_at_def.
    Proof.
      exact (fra_state_eq_correspondence _ _ _ _ (fra_replace_at_fun t'R t'L Ht') Hns).
    Qed.

    Definition src_rest_of_schedule_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_rest_of_schedule_invariant => s Job PStateR schedR t'R nsR)).
    Definition tgt_rest_of_schedule_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_rest_of_schedule_invariant
        Job dJ PStateL schedL t'L nsL)).
    Theorem rest_of_schedule_invariant_correspondence :
      PropSPropRel src_rest_of_schedule_invariant tgt_rest_of_schedule_invariant.
    Proof.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (fra_nat_neq_correspondence _ _ _ _ Ht Ht')|].
      exact (fra_state_eq_correspondence _ _ _ _ (fra_replace_at_fun tR tL Ht) (Hsched tR tL Ht)).
    Qed.

    Definition src_service_at_other_times_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_service_at_other_times_invariant => s Job PStateR schedR t'R nsR)).
    Definition tgt_service_at_other_times_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_service_at_other_times_invariant
        Job dJ PStateL schedL t'L nsL)).
    Theorem service_at_other_times_invariant_correspondence :
      PropSPropRel src_service_at_other_times_invariant tgt_service_at_other_times_invariant.
    Proof.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_imp_correspondence;
        [exact (fra_or_correspondence _ _ _ _ (sub_nat_le_correspondence _ _ _ _ Ht2 Ht')
          (sub_nat_lt_correspondence _ _ _ _ Ht' Ht1))|].
      apply ar_forall_identity_correspondence. intro j.
      exact (sub_nat_eq_correspondence _ _ _ _
        (fra_service_during_related _ _ Hsched j _ _ _ _ Ht1 Ht2)
        (fra_service_during_related _ _ fra_replace_at_fun j _ _ _ _ Ht1 Ht2)).
    Qed.

    Definition src_service_delta : Prop :=
      ltac:(body_of (fun s : S.statement_service_delta => s Job PStateR schedR t'R nsR)).
    Definition tgt_service_delta : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_service_delta
        Job dJ PStateL schedL t'L nsL)).
    Theorem service_delta_correspondence : PropSPropRel src_service_delta tgt_service_delta.
    Proof.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_imp_correspondence; [exact (fra_window_related _ _ _ _ Ht1 Ht2)|].
      apply ar_forall_identity_correspondence. intro j.
      exact (sub_nat_eq_correspondence _ _ _ _
        (svc_target_add_related _ _ _ _
          (fra_service_during_related _ _ Hsched j _ _ _ _ Ht1 Ht2)
          (fra_service_at_related _ _ fra_replace_at_fun j _ _ Ht'))
        (svc_target_add_related _ _ _ _
          (fra_service_during_related _ _ fra_replace_at_fun j _ _ _ _ Ht1 Ht2)
          (fra_service_at_related _ _ Hsched j _ _ Ht'))).
    Qed.

    Definition src_service_in_replaced : Prop :=
      ltac:(body_of (fun s : S.statement_service_in_replaced => s Job PStateR schedR t'R nsR)).
    Definition tgt_service_in_replaced : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_service_in_replaced
        Job dJ PStateL schedL t'L nsL)).
    Theorem service_in_replaced_correspondence :
      PropSPropRel src_service_in_replaced tgt_service_in_replaced.
    Proof.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_imp_correspondence; [exact (fra_window_related _ _ _ _ Ht1 Ht2)|].
      apply ar_forall_identity_correspondence. intro j.
      exact (sub_nat_eq_correspondence _ _ _ _
        (fra_service_during_related _ _ fra_replace_at_fun j _ _ _ _ Ht1 Ht2)
        (svc_target_sub_related _ _ _ _
          (svc_target_add_related _ _ _ _
            (fra_service_during_related _ _ Hsched j _ _ _ _ Ht1 Ht2)
            (fra_service_at_related _ _ fra_replace_at_fun j _ _ Ht'))
          (fra_service_at_related _ _ Hsched j _ _ Ht'))).
    Qed.

    Section Job.
      Variable j : Job.

      Definition src_service_at_of_others_invariant : Prop :=
        ltac:(body_of (fun s : S.statement_service_at_of_others_invariant => s Job PStateR schedR t'R nsR j)).
      Definition tgt_service_at_of_others_invariant : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_service_at_of_others_invariant
          Job dJ PStateL schedL t'L nsL j)).
      Theorem service_at_of_others_invariant_correspondence :
        PropSPropRel src_service_at_of_others_invariant tgt_service_at_of_others_invariant.
      Proof.
        apply ar_imp_correspondence; [exact (fra_not_scheduled_related _ _ fra_replace_at_fun j)|].
        apply ar_imp_correspondence; [exact (fra_not_scheduled_related _ _ Hsched j)|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        exact (sub_nat_eq_correspondence _ _ _ _
          (fra_service_at_related _ _ Hsched j _ _ Ht)
          (fra_service_at_related _ _ fra_replace_at_fun j _ _ Ht)).
      Qed.

      Definition src_service_during_of_others_invariant : Prop :=
        ltac:(body_of (fun s : S.statement_service_during_of_others_invariant => s Job PStateR schedR t'R nsR j)).
      Definition tgt_service_during_of_others_invariant : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_ReplaceAt_service_during_of_others_invariant
          Job dJ PStateL schedL t'L nsL j)).
      Theorem service_during_of_others_invariant_correspondence :
        PropSPropRel src_service_during_of_others_invariant tgt_service_during_of_others_invariant.
      Proof.
        apply ar_imp_correspondence; [exact (fra_not_scheduled_related _ _ fra_replace_at_fun j)|].
        apply ar_imp_correspondence; [exact (fra_not_scheduled_related _ _ Hsched j)|].
        apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
        apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
        exact (sub_nat_eq_correspondence _ _ _ _
          (fra_service_during_related _ _ Hsched j _ _ _ _ Ht1 Ht2)
          (fra_service_during_related _ _ fra_replace_at_fun j _ _ _ _ Ht1 Ht2)).
      Qed.
    End Job.
  End Replace.
End ReplaceAt.
