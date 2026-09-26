From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsRbfSemanticSource.
From prosa Require Import model.priority.coercion.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsRbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence.

Module I := ImportedFactsRbf.
Module S := FactsRbfSemanticSource.FactsRbfSemanticSource.
Module RB := RequestBoundFunctionSemanticSource.RequestBoundFunctionSemanticSource.
Module SC := SchedulabilitySemanticSource.SchedulabilitySemanticSource.
Module WB := WorkloadBoundedSemanticSource.WorkloadBoundedSemanticSource.

(** Statement correspondences for [analysis/facts/model/rbf.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, [task_cost], [job_task],
    [job_arrival], [job_cost], a leading [MaxArrivals] instance, a leading
    arrival sequence, task set, FP policy, processor state and schedule);
    target side: the imported Lean theorem types at related inputs
    ([SubNatRel] on [task_cost], the accepted [CvMaxArrivalsRel],
    [Lean.eq] on [job_task], [ArJobArrivalRel], [SvcJobCostRel],
    [ArArrivalSequenceRel], [ArListRel], FP policies pointwise on Booleans,
    the accepted two-sided [SvcProcessorStateRel]/[SvcScheduleRel]).  Every
    binder quantified inside a statement is covered in both directions: task
    sets and job/task predicates through the list and Boolean conversions,
    FP and JLFP policies pointwise, [MaxArrivals] instances by the accepted
    curve-family totals, processor models and their schedules by the
    processor-model cover of the accepted ideal service-of-jobs certificate
    (replayed here); tasks and jobs are identity carriers, Nats are covered
    in both directions.  RBFs, workloads, arrival curves and the
    workload bound are closed by the accepted request-bound-function,
    workload, arrival-curve and workload-bound certificates.  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma frbf_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma frbf_forall_cover_type (A B : Type) (Rel : A -> B -> Type)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma frbf_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma frbf_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma frbf_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma frbf_bool_rel_true (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> is_true bR -> Lean.eq bL I.Bool_true.
Proof.
  intros H Hb. destruct bR.
  - exact (sub_imported_eq_sym _ _ H).
  - discriminate Hb.
Qed.

Lemma frbf_bool_false_of_rocq (b : I.Bool) : ~~ svc_bool_to_rocq b -> Lean.eq b I.Bool_false.
Proof.
  destruct b; cbn; intro H; first [exact (@Lean.eq_refl _ _) | discriminate H].
Qed.

Definition frbf_exists_elim_sprop (T : finType) (p : pred T) (Q : SProp)
    (HQ : forall x, p x -> Q) (H : [exists x, p x]) : Q :=
  match elimT existsP H with ex_intro x Hx => HQ x Hx end.

Fixpoint frbf_map_values_canonical (C : Type) (f : C -> nat) (xs : seq C) :
    Lean.eq (svc_nat_list_to_imported (map f xs))
      (I.List_map_inst2 C Lean.Nat (fun c => sub_nat_to_imported (f c)) (svc_list_to_imported xs)) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported (f x))) _ _
      (frbf_map_values_canonical C f tail)
  end.

Fixpoint frbf_ar_svc_list_eq {T : Type} (xs : seq T) :
    Lean.eq (ar_list_to_imported xs) (svc_list_to_imported xs) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons T x) _ _ (frbf_ar_svc_list_eq tail)
  end.

Lemma frbf_monotone_related (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel (@prosa.util.rel.monotone nat leq fR)
    (I.Prosa_Util_Rel_monotone Lean.Nat (fun x y => ar_target_decide_le x y) fL).
Proof.
  intro Hf. unfold prosa.util.rel.monotone.
  cbn [I.Prosa_Util_Rel_monotone].
  apply ar_forall_nat_correspondence. intros xR xL Hx.
  apply ar_forall_nat_correspondence. intros yR yL Hy.
  apply ar_imp_correspondence;
    [exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ Hx Hy))|].
  exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy))).
Qed.

(** ** Processor-model cover (replayed from the accepted ideal
    service-of-jobs certificate) *)

Section PSCover.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSL := I.Prosa_Behavior_Schedule_ProcessorState Job dJ.

  Record FrbfPSRel (PR : prosa.behavior.schedule.ProcessorState Job) (PL : PSL) : Type := {
    frbf_st_to : @prosa.behavior.schedule.State Job PR ->
      I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL;
    frbf_st_from : I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL ->
      @prosa.behavior.schedule.State Job PR;
    frbf_st_rt_source : forall s, Logic.eq (frbf_st_from (frbf_st_to s)) s;
    frbf_st_rt_target : forall s, Lean.eq (frbf_st_to (frbf_st_from s)) s;
    frbf_co_to : @prosa.behavior.schedule.Core Job PR ->
      I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL;
    frbf_co_from : I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL ->
      @prosa.behavior.schedule.Core Job PR;
    frbf_co_rt_target : forall c, Lean.eq (frbf_co_to (frbf_co_from c)) c;
    frbf_sch_rel : forall j s c,
      SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PR j s c)
        (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job dJ PL j (frbf_st_to s) (frbf_co_to c));
    frbf_srv_in_rel : forall j s,
      SubNatRel (@prosa.behavior.schedule.service_in Job PR j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j (frbf_st_to s));
    frbf_sup_in_rel : forall s,
      SubNatRel (@prosa.behavior.schedule.supply_in Job PR s)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL (frbf_st_to s)) }.
  Arguments frbf_st_to {PR PL} _.
  Arguments frbf_st_from {PR PL} _.
  Arguments frbf_st_rt_source {PR PL} _.
  Arguments frbf_st_rt_target {PR PL} _.
  Arguments frbf_co_to {PR PL} _.
  Arguments frbf_co_from {PR PL} _.
  Arguments frbf_co_rt_target {PR PL} _.
  Arguments frbf_sch_rel {PR PL} _.
  Arguments frbf_srv_in_rel {PR PL} _.
  Arguments frbf_sup_in_rel {PR PL} _.

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : PSL.
    Variable X : FrbfPSRel PR PL.

    Definition FrbfPSchedRel (schedR : @prosa.behavior.schedule.schedule Job PR)
        (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PL) : SProp :=
      forall tR tL, SubNatRel tR tL -> Lean.eq (frbf_st_to X (schedR tR)) (schedL tL).

    Definition frbf_psr_sched_to_target (schedR : @prosa.behavior.schedule.schedule Job PR) :
        I.Prosa_Behavior_Schedule_schedule Job dJ PL :=
      fun tL => frbf_st_to X (schedR (sub_nat_to_rocq tL)).

    Definition frbf_psr_sched_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PL) :
        @prosa.behavior.schedule.schedule Job PR :=
      fun tR => frbf_st_from X (schedL (sub_nat_to_imported tR)).

    Lemma frbf_psr_sched_to_target_rel schedR : FrbfPSchedRel schedR (frbf_psr_sched_to_target schedR).
    Proof.
      intros tR tL Ht. unfold frbf_psr_sched_to_target.
      rewrite (frbf_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
    Qed.

    Lemma frbf_psr_sched_to_source_rel schedL : FrbfPSchedRel (frbf_psr_sched_to_source schedL) schedL.
    Proof.
      intros tR tL Ht. unfold frbf_psr_sched_to_source.
      exact (sub_imported_eq_trans _ _ _ (frbf_st_rt_target X _) (sub_imported_eq_congr schedL _ _ Ht)).
    Qed.

    Definition frbf_cover_psched :=
      frbf_forall_cover_sprop _ _ FrbfPSchedRel frbf_psr_sched_to_target frbf_psr_sched_to_source
        frbf_psr_sched_to_target_rel frbf_psr_sched_to_source_rel.

    Section PSched.
      Variable schedR : @prosa.behavior.schedule.schedule Job PR.
      Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
      Hypothesis Hs : FrbfPSchedRel schedR schedL.

      Lemma frbf_psr_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SubNatRel (@prosa.behavior.service.service_at Job PR schedR j tR)
          (I.Prosa_Behavior_Service_service_at Job dJ PL schedL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.service_at.
        cbn [I.Prosa_Behavior_Service_service_at].
        exact (frbf_lean_transport
          (fun sL => SubNatRel (@prosa.behavior.schedule.service_in Job PR j (schedR tR))
             (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j sL))
          _ _ (Hs tR tL Ht) (frbf_srv_in_rel X j (schedR tR))).
      Qed.

      Lemma frbf_psr_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SubNatRel (@prosa.behavior.service.service Job PR schedR j tR)
          (I.Prosa_Behavior_Service_service Job dJ PL schedL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.service.
        cbn [I.Prosa_Behavior_Service_service].
        have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
          (fun t => @prosa.behavior.service.service_at Job PR schedR j t)
          (fun t => I.Prosa_Behavior_Service_service_at Job dJ PL schedL j t)
          (sub_nat_rel_canonical O) Ht (fun xR xL Hx => frbf_psr_service_at_related j xR xL Hx).
        change (SubNatRel
          (@prosa.behavior.service.service_during Job PR schedR j O tR)
          (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
            Job dJ PL schedL j Lean.Nat_zero tL)) in Hsum.
        exact Hsum.
      Qed.
    End PSched.
  End Pair.

  Section ToTarget.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Let CR := @prosa.behavior.schedule.Core Job PR.
    Let enumL : I.List CR := svc_list_to_imported (enum CR).

    Lemma frbf_enum_nodup : I.List_Nodup CR enumL.
    Proof.
      exact (frbf_lean_transport (fun l => I.List_Nodup CR l) _ _ (frbf_ar_svc_list_eq (enum CR))
        (ar_uniq_truth_forward CR (enum CR) (sub_nat_prop_to_truth _ (enum_uniq CR)))).
    Qed.

    Lemma frbf_enum_complete : forall c : CR, ar_target_mem c enumL.
    Proof.
      intro c.
      exact (prop_to_sprop _ _ (ar_membership_correspondence CR c (enum CR) enumL
        (frbf_ar_svc_list_eq (enum CR))) (mem_enum CR c)).
    Qed.

    Lemma frbf_law_le : forall j s r,
      I.LE_le_inst1 I.Prosa_Behavior_Job_work I.instLENat
        (sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s r))
        (sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s r)).
    Proof.
      intros j s r.
      exact (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _
        (sub_nat_rel_canonical _) (sub_nat_rel_canonical _))
        (@prosa.behavior.schedule.service_on_le_supply_on Job PR j s r)).
    Qed.

    Lemma frbf_law_zero : forall j s r,
      Lean.eq (svc_bool_to_imported (@prosa.behavior.schedule.scheduled_on Job PR j s r)) I.Bool_false ->
      Lean.eq (sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s r))
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)).
    Proof.
      intros j s r H.
      destruct (@prosa.behavior.schedule.scheduled_on Job PR j s r) eqn:E.
      - exact (svc_false_elim _ (svc_false_ne_true (sub_imported_eq_sym _ _ H))).
      - have Z := @prosa.behavior.schedule.service_on_implies_scheduled_on Job PR j s r (negbT E).
        exact (frbf_lean_transport (fun n => Lean.eq (sub_nat_to_imported n)
            (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)))
          _ _ (coq_eq_to_imported_eq _ _ (Logic.eq_sym Z)) (sub_nat_rel_canonical O)).
    Qed.

    Definition frbf_ps_to_target : PSL :=
      I.Prosa_Behavior_Schedule_ProcessorState_mk Job dJ
        (@prosa.behavior.schedule.State Job PR) CR
        (I.Prosa_Validation_ProcessorStateCoverInterface_fintypeOfNodupListing CR enumL
          frbf_enum_nodup frbf_enum_complete)
        (ar_decidable_eq CR)
        (fun j s c => svc_bool_to_imported (@prosa.behavior.schedule.scheduled_on Job PR j s c))
        (fun s c => sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s c))
        (fun j s c => sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s c))
        frbf_law_le frbf_law_zero.

    Lemma frbf_to_target_service_in (j : Job) (s : @prosa.behavior.schedule.State Job PR) :
      SubNatRel (@prosa.behavior.schedule.service_in Job PR j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ frbf_ps_to_target j s).
    Proof.
      unfold prosa.behavior.schedule.service_in. rewrite -big_enum.
      rewrite (svc_mathcomp_big_seq_as_fold_core CR (enum CR)).
      change (SubNatRel (foldr addn O (map (fun c => @prosa.behavior.schedule.service_on Job PR j s c) (enum CR)))
        (svc_target_list_sum (I.List_map_inst2 CR Lean.Nat
          (fun c => sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s c))
          (svc_list_to_imported (enum CR))))).
      apply svc_list_sum_related.
      exact (frbf_map_values_canonical CR _ (enum CR)).
    Qed.

    Lemma frbf_to_target_supply_in (s : @prosa.behavior.schedule.State Job PR) :
      SubNatRel (@prosa.behavior.schedule.supply_in Job PR s)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ frbf_ps_to_target s).
    Proof.
      unfold prosa.behavior.schedule.supply_in. rewrite -big_enum.
      rewrite (svc_mathcomp_big_seq_as_fold_core CR (enum CR)).
      change (SubNatRel (foldr addn O (map (fun c => @prosa.behavior.schedule.supply_on Job PR s c) (enum CR)))
        (svc_target_list_sum (I.List_map_inst2 CR Lean.Nat
          (fun c => sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s c))
          (svc_list_to_imported (enum CR))))).
      apply svc_list_sum_related.
      exact (frbf_map_values_canonical CR _ (enum CR)).
    Qed.

    Definition frbf_rel_to_target : FrbfPSRel PR frbf_ps_to_target :=
      Build_FrbfPSRel PR frbf_ps_to_target
        (fun s : @prosa.behavior.schedule.State Job PR => s)
        (fun s : @prosa.behavior.schedule.State Job PR => s)
        (fun s => Logic.eq_refl s) (fun s => @Lean.eq_refl _ s)
        (fun c : CR => c) (fun c : CR => c) (fun c => @Lean.eq_refl _ c)
        (fun j s c => @Lean.eq_refl _ _)
        frbf_to_target_service_in frbf_to_target_supply_in.
  End ToTarget.

  Section ToSource.
    Variable PL : PSL.
    Let CL := I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL.
    Let SL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL.
    Let decL := I.Prosa_Behavior_Schedule_ProcessorState_coreDecidableEq Job dJ PL.

    Definition frbf_core_eqb (x y : CL) : bool :=
      svc_bool_to_rocq (I.Decidable_decide (Lean.eq x y) (decL x y)).

    Lemma frbf_core_eqP : Equality.axiom frbf_core_eqb.
    Proof.
      intros x y. unfold frbf_core_eqb.
      destruct (decL x y) as [Hne | He]; cbn.
      - apply ReflectF. intro E. destruct E.
        exact (match Hne (@Lean.eq_refl _ x) with end).
      - apply ReflectT. exact (imported_eq_to_coq_eq _ _ He).
    Qed.

    Definition frbf_core_eqType : eqType := HB.pack CL (hasDecEq.Build CL frbf_core_eqP).

    Definition frbf_core_list : seq frbf_core_eqType :=
      ar_list_to_rocq (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL).

    Lemma frbf_core_list_rel :
      ArListRel frbf_core_list (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL).
    Proof. exact (ar_list_target_roundtrip _). Qed.

    Lemma frbf_core_list_uniq : uniq frbf_core_list.
    Proof.
      exact (sprop_to_prop _ _ (ar_uniq_correspondence frbf_core_eqType _ _ frbf_core_list_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_nodup Job dJ PL)).
    Qed.

    Lemma frbf_core_list_complete (c : CL) : (c : frbf_core_eqType) \in frbf_core_list.
    Proof.
      exact (sprop_to_prop _ _ (ar_membership_correspondence frbf_core_eqType c _ _ frbf_core_list_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_complete Job dJ PL c)).
    Qed.

    Definition frbf_core_finType : finType := adhoc_seq_sub_finType frbf_core_list.

    Definition frbf_core_from (c : CL) : frbf_core_finType :=
      @SeqSub frbf_core_eqType frbf_core_list c (frbf_core_list_complete c).

    Lemma frbf_core_enum_map : map (@ssval frbf_core_eqType frbf_core_list) (enum frbf_core_finType) = frbf_core_list.
    Proof. rewrite enumT unlock /=. exact (val_seq_sub_enum frbf_core_list_uniq). Qed.

    Definition frbf_src_scheduled_on (j : Job) (s : SL) (c : frbf_core_finType) : bool :=
      svc_bool_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job dJ PL j s (ssval c)).
    Definition frbf_src_supply_on (s : SL) (c : frbf_core_finType) : nat :=
      sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PL s (ssval c)).
    Definition frbf_src_service_on (j : Job) (s : SL) (c : frbf_core_finType) : nat :=
      sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s (ssval c)).

    Lemma frbf_src_law_le j s r : leq (frbf_src_service_on j s r) (frbf_src_supply_on s r).
    Proof.
      exact (sprop_to_prop _ _ (sub_nat_le_correspondence _ _ _ _
        (sub_nat_rel_surjective _) (sub_nat_rel_surjective _))
        (I.service_on_le_supply_on Job dJ PL j s (ssval r))).
    Qed.

    Lemma frbf_src_law_zero j s r : ~~ frbf_src_scheduled_on j s r -> frbf_src_service_on j s r = O.
    Proof.
      unfold frbf_src_scheduled_on, frbf_src_service_on. intro H.
      have E : sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s (ssval r))
          = sub_nat_to_rocq (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)) :=
        f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _
          (I.service_on_implies_scheduled_on Job dJ PL j s (ssval r) (frbf_bool_false_of_rocq _ H))).
      rewrite E. exact (sub_nat_rocq_roundtrip O).
    Qed.

    Definition frbf_ps_to_source : prosa.behavior.schedule.ProcessorState Job :=
      @prosa.behavior.schedule.Build_ProcessorState Job SL frbf_core_finType
        frbf_src_scheduled_on frbf_src_supply_on frbf_src_service_on
        frbf_src_law_le frbf_src_law_zero.

    Lemma frbf_core_enumeration_rel :
      SvcCoreEnumerationRel frbf_core_finType CL (@ssval frbf_core_eqType frbf_core_list)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL).
    Proof.
      unfold SvcCoreEnumerationRel. rewrite frbf_core_enum_map.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (frbf_ar_svc_list_eq _))
        frbf_core_list_rel).
    Qed.

    Lemma frbf_to_source_service_in (j : Job) (s : SL) :
      SubNatRel (@prosa.behavior.schedule.service_in Job frbf_ps_to_source j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j s).
    Proof.
      have Hsum := svc_finite_sum_related frbf_core_finType CL (@ssval frbf_core_eqType frbf_core_list)
        (fun c => frbf_src_service_on j s c)
        (fun c => I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s c)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL)
        (fun c => sub_nat_rel_surjective _) frbf_core_enumeration_rel.
      exact (sub_imported_eq_trans _ _ _ Hsum (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ScheduleInterface_production_service_in_as_list_sum Job dJ PL j s))).
    Qed.

    Lemma frbf_to_source_supply_in (s : SL) :
      SubNatRel (@prosa.behavior.schedule.supply_in Job frbf_ps_to_source s)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL s).
    Proof.
      have Hsum := svc_finite_sum_related frbf_core_finType CL (@ssval frbf_core_eqType frbf_core_list)
        (fun c => frbf_src_supply_on s c)
        (fun c => I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PL s c)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL)
        (fun c => sub_nat_rel_surjective _) frbf_core_enumeration_rel.
      exact (sub_imported_eq_trans _ _ _ Hsum (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum Job dJ PL s))).
    Qed.

    Definition frbf_rel_to_source : FrbfPSRel frbf_ps_to_source PL :=
      Build_FrbfPSRel frbf_ps_to_source PL
        (fun s : SL => s) (fun s : SL => s)
        (fun s => Logic.eq_refl s) (fun s => @Lean.eq_refl _ s)
        (fun c : frbf_core_finType => ssval c) frbf_core_from (fun c => @Lean.eq_refl _ c)
        (fun j s c => svc_bool_target_roundtrip _)
        frbf_to_source_service_in frbf_to_source_supply_in.
  End ToSource.

  Definition frbf_cover_pstate :=
    frbf_forall_cover_type _ _ FrbfPSRel frbf_ps_to_target frbf_ps_to_source
      frbf_rel_to_target frbf_rel_to_source.
End PSCover.

(** ** Statements *)

Section Facts.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  (** *** Covers *)

  Lemma frbf_list_to_target_rel (xs : seq Task) : ArListRel xs (ar_list_to_imported xs).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Lemma frbf_list_to_source_rel (xs : I.List Task) : ArListRel (ar_list_to_rocq xs) xs.
  Proof. exact (ar_list_target_roundtrip xs). Qed.

  Let cover_ts :=
    frbf_forall_cover_sprop _ _ (@ArListRel Task)
      ar_list_to_imported ar_list_to_rocq frbf_list_to_target_rel frbf_list_to_source_rel.

  Definition frbf_pred_to_source {T : Type} (PL : T -> I.Bool) : pred T :=
    fun x => ar_bool_to_rocq (PL x).

  Lemma frbf_pred_to_source_rel {T : Type} (PL : T -> I.Bool) :
    ArPredRel (frbf_pred_to_source PL) PL.
  Proof. intro x. exact (ar_bool_target_roundtrip (PL x)). Qed.

  Let cover_jpred :=
    frbf_forall_cover_sprop _ _ (@ArPredRel Job)
      (@ar_pred_to_imported Job) (@frbf_pred_to_source Job)
      (@ar_pred_canonical Job) (@frbf_pred_to_source_rel Job).

  Let cover_tpred :=
    frbf_forall_cover_sprop _ _ (@ArPredRel Task)
      (@ar_pred_to_imported Task) (@frbf_pred_to_source Task)
      (@ar_pred_canonical Task) (@frbf_pred_to_source_rel Task).

  Definition FrbfFPRel (fpR : prosa.model.priority.definitions.FP_policy Task)
      (fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) : SProp :=
    forall x y : Task,
      ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
        (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Definition frbf_fp_to_target (fpR : prosa.model.priority.definitions.FP_policy Task) :
      I.Prosa_Model_Priority_Definitions_FP_policy Task dT :=
    I.Prosa_Model_Priority_Definitions_FP_policy_mk Task dT
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task fpR x y)).

  Definition frbf_fp_to_source (fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) :
      prosa.model.priority.definitions.FP_policy Task :=
    fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Lemma frbf_fp_to_target_rel fpR : FrbfFPRel fpR (frbf_fp_to_target fpR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma frbf_fp_to_source_rel fpL : FrbfFPRel (frbf_fp_to_source fpL) fpL.
  Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

  Let cover_fp :=
    frbf_forall_cover_sprop _ _ FrbfFPRel frbf_fp_to_target frbf_fp_to_source
      frbf_fp_to_target_rel frbf_fp_to_source_rel.

  Definition FrbfJLFPRel (pR : prosa.model.priority.definitions.JLFP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) : SProp :=
    forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Definition frbf_jlfp_to_target (pR : prosa.model.priority.definitions.JLFP_policy Job) :
      I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ :=
    I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)).

  Definition frbf_jlfp_to_source (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) :
      prosa.model.priority.definitions.JLFP_policy Job :=
    fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma frbf_jlfp_to_target_rel pR : FrbfJLFPRel pR (frbf_jlfp_to_target pR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma frbf_jlfp_to_source_rel pL : FrbfJLFPRel (frbf_jlfp_to_source pL) pL.
  Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

  Let cover_jlfp :=
    frbf_forall_cover_sprop _ _ FrbfJLFPRel frbf_jlfp_to_target frbf_jlfp_to_source
      frbf_jlfp_to_target_rel frbf_jlfp_to_source_rel.

  Let cover_ma :=
    frbf_forall_cover_sprop _ _ (CvMaxArrivalsRel Task)
      (fun cR => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT (fun tsk => cv_import_fun (cR tsk)))
      (fun cL => (fun tsk => cv_export_fun (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk))
         : prosa.model.task.arrival.curves.MaxArrivals Task)
      (MaxArrivals_source_total Task) (MaxArrivals_target_total Task).

  (** *** Task-concept predicates *)

  Lemma frbf_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (frbf_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (frbf_decide_eq_related Task _ tsk).
  Qed.

  Lemma frbf_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (frbf_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma frbf_valid_job_costs_related :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    unfold prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (frbf_task_cost_of_job_related j))).
  Qed.

  Lemma frbf_all_jobs_from_taskset_related tsR tsL (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
  Qed.

  Lemma frbf_hep_task_jobs fpR fpL (Hfp : FrbfFPRel fpR fpL) (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job
        (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fpR) x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ
        (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fpL) x y).
  Proof.
    unfold ArBoolRel.
    exact (sub_imported_eq_trans _ _ _ (Hfp _ _)
      (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
        _ _ _ _ (Hjt x) (Hjt y))).
  Qed.

  Lemma frbf_reflexive_task_related fpR fpL (Hfp : FrbfFPRel fpR fpL) :
    PropSPropRel (@prosa.model.priority.definitions.reflexive_task_priorities Task fpR)
      (I.Prosa_Model_Priority_Definitions_reflexive_task_priorities Task dT fpL).
  Proof.
    unfold prosa.model.priority.definitions.reflexive_task_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_task_priorities].
    apply ar_forall_identity_correspondence. intro tsk.
    exact (ar_bool_truth_correspondence _ _ (Hfp tsk tsk)).
  Qed.

  Let RBF maR maL Hma := task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma.

  Lemma frbf_max1_positive_related maR maL (Hma : CvMaxArrivalsRel Task maR maL) (tsk : Task) :
    PropSPropRel (is_true (ltn O (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk (S O))))
      (ar_target_lt Lean.Nat_zero (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk
        (Lean.Nat_succ Lean.Nat_zero))).
  Proof.
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (Hma tsk (S O) _ (sub_nat_rel_canonical (S O)))).
  Qed.

  (** *** Statements over a leading [MaxArrivals] instance *)

  Section MA.
    Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
    Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
    Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

    Let RESP tsk := respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hma tsk).
    Let RESPS tsR tsL Hts :=
      taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
        maR maL Hma.
    Let TWB tsk t1R t1L t2R t2L H1 H2 :=
      task_workload_between_correspondence Job costR costL Hcost arrR arrL Harr Task jtR jtL Hjt
        tsk t1R t1L t2R t2L H1 H2.

    Definition src_rbf_spec : Prop :=
      ltac:(body_of (fun s : S.statement_rbf_spec => s Task tcR maR Job jtR costR arrR)).
    Definition tgt_rbf_spec : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_rbf_spec
        Task dT tcL maL Job dJ jtL costL arrL)).
    Theorem rbf_spec_correspondence : PropSPropRel src_rbf_spec tgt_rbf_spec.
    Proof.
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (RESP tsk)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      exact (sub_nat_le_correspondence _ _ _ _
        (TWB tsk _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
        (RBF maR maL Hma tsk _ _ Hd)).
    Qed.

    Definition src_rbf_spec' : Prop :=
      ltac:(body_of (fun s : S.statement_rbf_spec' => s Task tcR maR Job jtR costR arrR)).
    Definition tgt_rbf_spec' : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_rbf_spec'
        Task dT tcL maL Job dJ jtL costL arrL)).
    Theorem rbf_spec'_correspondence : PropSPropRel src_rbf_spec' tgt_rbf_spec'.
    Proof.
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply cover_jpred. intros PR PL HP.
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (RESP tsk)|].
      apply ar_imp_correspondence.
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP j))|].
        exact (ar_bool_truth_correspondence _ _ (frbf_job_of_task_related tsk j)).
      - apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_forall_nat_correspondence. intros dR dL Hd.
        exact (sub_nat_le_correspondence _ _ _ _
          (workload_of_jobs_correspondence Job costR costL Hcost PR PL HP _ _
            (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht
              (svc_target_add_related _ _ _ _ Ht Hd)))
          (RBF maR maL Hma tsk _ _ Hd)).
    Qed.

    Definition src_total_workload_le_total_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_total_workload_le_total_rbf => s Task tcR maR Job jtR costR arrR)).
    Definition tgt_total_workload_le_total_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_total_workload_le_total_rbf
        Task dT tcL maL Job dJ jtL costL arrL)).
    Theorem total_workload_le_total_rbf_correspondence :
      PropSPropRel src_total_workload_le_total_rbf tgt_total_workload_le_total_rbf.
    Proof.
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (frbf_all_jobs_from_taskset_related tsR tsL Hts)|].
      apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      exact (sub_nat_le_correspondence _ _ _ _
        (total_workload_between_correspondence Job costR costL Hcost arrR arrL Harr _ _ _ _ Ht
          (svc_target_add_related _ _ _ _ Ht Hd))
        (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _ Hd)).
    Qed.

    Definition src_workload_of_jobs_bounded : Prop :=
      ltac:(body_of (fun s : S.statement_workload_of_jobs_bounded => s Task tcR maR Job jtR costR arrR)).
    Definition tgt_workload_of_jobs_bounded : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_workload_of_jobs_bounded
        Task dT tcL maL Job dJ jtL costL arrL)).
    Theorem workload_of_jobs_bounded_correspondence :
      PropSPropRel src_workload_of_jobs_bounded tgt_workload_of_jobs_bounded.
    Proof.
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (frbf_all_jobs_from_taskset_related tsR tsL Hts)|].
      apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
      apply cover_jpred. intros P1R P1L HP1.
      apply cover_tpred. intros P2R P2L HP2.
      apply ar_imp_correspondence.
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP1 j))|].
        rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
        exact (ar_bool_truth_correspondence _ _ (HP2 _)).
      - apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_forall_nat_correspondence. intros dR dL Hd.
        exact (sub_nat_le_correspondence _ _ _ _
          (workload_of_jobs_correspondence Job costR costL Hcost P1R P1L HP1 _ _
            (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht
              (svc_target_add_related _ _ _ _ Ht Hd)))
          (rbf_sum_filtered_related Task _ _ (fun tsk => RBF maR maL Hma tsk _ _ Hd) P2R P2L HP2 _ _ Hts)).
    Qed.

    Section Sched.
      Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
      Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
      Variable R : SvcProcessorStateRel Job PStateR PStateL.
      Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
      Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
      Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

      Definition src_athep_workload_le_total_ohep_rbf : Prop :=
        ltac:(body_of (fun s : S.statement_athep_workload_le_total_ohep_rbf =>
          s Task tcR maR Job jtR jaR costR arrR PStateR schedR)).
      Definition tgt_athep_workload_le_total_ohep_rbf : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_athep_workload_le_total_ohep_rbf
          Task dT tcL maL Job dJ jtL jaL costL arrL PStateL schedL)).
      Theorem athep_workload_le_total_ohep_rbf_correspondence :
        PropSPropRel src_athep_workload_le_total_ohep_rbf tgt_athep_workload_le_total_ohep_rbf.
      Proof.
        apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
        apply cover_ts. intros tsR tsL Hts.
        apply ar_imp_correspondence; [exact (frbf_all_jobs_from_taskset_related tsR tsL Hts)|].
        apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
        apply cover_fp. intros fpR fpL Hfp.
        apply ar_forall_identity_correspondence. intro tsk.
        exact (athep_workload_is_bounded_correspondence Task Job costR costL Hcost jaR jaL Hja
          jtR jtL Hjt PStateR PStateL R _ _ (frbf_hep_task_jobs fpR fpL Hfp) arrR arrL Harr
          schedR schedL Hsched tsk _ _
          (fun aR aL dR dL _ Hd => total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc
            maR maL Hma tsR tsL Hts fpR fpL Hfp tsk dR dL Hd)).
      Qed.
    End Sched.

    Definition src_hep_workload_le_total_hep_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_hep_workload_le_total_hep_rbf => s Task tcR maR Job jtR costR arrR)).
    Definition tgt_hep_workload_le_total_hep_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_hep_workload_le_total_hep_rbf
        Task dT tcL maL Job dJ jtL costL arrL)).
    Theorem hep_workload_le_total_hep_rbf_correspondence :
      PropSPropRel src_hep_workload_le_total_hep_rbf tgt_hep_workload_le_total_hep_rbf.
    Proof.
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (frbf_all_jobs_from_taskset_related tsR tsL Hts)|].
      apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
      apply cover_fp. intros fpR fpL Hfp.
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frbf_job_of_task_related tsk j))|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      exact (sub_nat_le_correspondence _ _ _ _
        (workload_of_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr _ _
          (frbf_hep_task_jobs fpR fpL Hfp) j _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
        (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fpR fpL Hfp tsk _ _ Hd)).
    Qed.

    Definition src_hep_workload_le_total_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_hep_workload_le_total_rbf => s Task tcR maR Job jtR costR arrR)).
    Definition tgt_hep_workload_le_total_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_hep_workload_le_total_rbf
        Task dT tcL maL Job dJ jtL costL arrL)).
    Theorem hep_workload_le_total_rbf_correspondence :
      PropSPropRel src_hep_workload_le_total_rbf tgt_hep_workload_le_total_rbf.
    Proof.
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (frbf_all_jobs_from_taskset_related tsR tsL Hts)|].
      apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      exact (sub_nat_le_correspondence _ _ _ _
        (workload_of_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht
          (svc_target_add_related _ _ _ _ Ht Hd))
        (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _ Hd)).
    Qed.

    (** Task-set statements *)

    Let VALIDTS tsR tsL (Hts : ArListRel tsR tsL) :=
      valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma.

    Definition src_total_rbf_monotone : Prop :=
      ltac:(body_of (fun s : S.statement_total_rbf_monotone => s Task tcR maR)).
    Definition tgt_total_rbf_monotone : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_total_rbf_monotone Task dT tcL maL)).
    Theorem total_rbf_monotone_correspondence :
      PropSPropRel src_total_rbf_monotone tgt_total_rbf_monotone.
    Proof.
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (VALIDTS tsR tsL Hts)|].
      apply frbf_monotone_related. intros dR dL Hd.
      exact (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _ Hd).
    Qed.

    Definition src_total_hep_rbf_monotone : Prop :=
      ltac:(body_of (fun s : S.statement_total_hep_rbf_monotone => s Task tcR maR)).
    Definition tgt_total_hep_rbf_monotone : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_total_hep_rbf_monotone Task dT tcL maL)).
    Theorem total_hep_rbf_monotone_correspondence :
      PropSPropRel src_total_hep_rbf_monotone tgt_total_hep_rbf_monotone.
    Proof.
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (VALIDTS tsR tsL Hts)|].
      apply cover_fp. intros fpR fpL Hfp.
      apply ar_forall_identity_correspondence. intro tsk.
      apply frbf_monotone_related. intros dR dL Hd.
      exact (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
        fpR fpL Hfp tsk _ _ Hd).
    Qed.

    Definition src_total_ohep_rbf_monotone : Prop :=
      ltac:(body_of (fun s : S.statement_total_ohep_rbf_monotone => s Task tcR maR)).
    Definition tgt_total_ohep_rbf_monotone : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_total_ohep_rbf_monotone Task dT tcL maL)).
    Theorem total_ohep_rbf_monotone_correspondence :
      PropSPropRel src_total_ohep_rbf_monotone tgt_total_ohep_rbf_monotone.
    Proof.
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (VALIDTS tsR tsL Hts)|].
      apply cover_fp. intros fpR fpL Hfp.
      apply ar_forall_identity_correspondence. intro tsk.
      apply frbf_monotone_related. intros dR dL Hd.
      exact (total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
        fpR fpL Hfp tsk _ _ Hd).
    Qed.

    Definition src_total_ohep_rbf0 : Prop :=
      ltac:(body_of (fun s : S.statement_total_ohep_rbf0 => s Task tcR maR)).
    Definition tgt_total_ohep_rbf0 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_total_ohep_rbf0 Task dT tcL maL)).
    Theorem total_ohep_rbf0_correspondence :
      PropSPropRel src_total_ohep_rbf0 tgt_total_ohep_rbf0.
    Proof.
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (VALIDTS tsR tsL Hts)|].
      apply cover_fp. intros fpR fpL Hfp.
      apply ar_forall_identity_correspondence. intro tsk.
      exact (sub_nat_eq_correspondence _ _ _ _
        (total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fpR fpL Hfp tsk _ _ (sub_nat_rel_canonical O))
        (sub_nat_rel_canonical O)).
    Qed.

    Definition src_hep_rbf_taskwise_partitioning : Prop :=
      ltac:(body_of (fun s : S.statement_hep_rbf_taskwise_partitioning => s Task tcR maR)).
    Definition tgt_hep_rbf_taskwise_partitioning : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_hep_rbf_taskwise_partitioning Task dT tcL maL)).
    Theorem hep_rbf_taskwise_partitioning_correspondence :
      PropSPropRel src_hep_rbf_taskwise_partitioning tgt_hep_rbf_taskwise_partitioning.
    Proof.
      apply cover_fp. intros fpR fpL Hfp.
      apply cover_ts. intros tsR tsL Hts.
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      apply sub_nat_eq_correspondence.
      - exact (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fpR fpL Hfp tsk _ _ Hd).
      - apply svc_target_add_related.
        + exact (total_hp_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
            fpR fpL Hfp tsk _ _ Hd).
        + exact (total_ep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
            fpR fpL Hfp tsk _ _ Hd).
    Qed.

    Ltac frbf_split_prefix :=
      apply cover_fp; let fpR := fresh "fpR" in let fpL := fresh "fpL" in
        let Hfp := fresh "Hfp" in intros fpR fpL Hfp;
      apply cover_ts; let tsR := fresh "tsR" in let tsL := fresh "tsL" in
        let Hts := fresh "Hts" in intros tsR tsL Hts;
      apply ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk;
      apply ar_imp_correspondence; [exact (frbf_reflexive_task_related fpR fpL Hfp)|];
      apply ar_forall_nat_correspondence; let dR := fresh "dR" in let dL := fresh "dL" in
        let Hd := fresh "Hd" in intros dR dL Hd;
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].

    Definition src_split_hep_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_split_hep_rbf => s Task tcR maR)).
    Definition tgt_split_hep_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_split_hep_rbf Task dT tcL maL)).
    Theorem split_hep_rbf_correspondence : PropSPropRel src_split_hep_rbf tgt_split_hep_rbf.
    Proof.
      frbf_split_prefix.
      apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
      apply sub_nat_eq_correspondence.
      - exact (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fpR fpL Hfp tsk _ _ Hd).
      - apply svc_target_add_related.
        + exact (total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
            fpR fpL Hfp tsk _ _ Hd).
        + exact (RBF maR maL Hma tsk _ _ Hd).
    Qed.

    Definition src_split_hep_rbf_weaken : Prop :=
      ltac:(body_of (fun s : S.statement_split_hep_rbf_weaken => s Task tcR maR)).
    Definition tgt_split_hep_rbf_weaken : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_split_hep_rbf_weaken Task dT tcL maL)).
    Theorem split_hep_rbf_weaken_correspondence :
      PropSPropRel src_split_hep_rbf_weaken tgt_split_hep_rbf_weaken.
    Proof.
      frbf_split_prefix.
      apply sub_nat_le_correspondence.
      - apply svc_target_add_related.
        + exact (total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
            fpR fpL Hfp tsk _ _ Hd).
        + exact (RBF maR maL Hma tsk _ _ Hd).
      - exact (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fpR fpL Hfp tsk _ _ Hd).
    Qed.

    (** Pathological RBFs: processor models quantified inside the statements *)

    Section TS.
      Variable tsR : seq Task.
      Variable tsL : I.List Task.
      Hypothesis Hts : ArListRel tsR tsL.

      Lemma frbf_task_response_time_bound_related PR PL (X : FrbfPSRel Job PR PL)
          schedR schedL (Hs : FrbfPSchedRel Job PR PL X schedR schedL) (tsk : Task)
          (rR : nat) (rL : Lean.Nat) (Hr : SubNatRel rR rL) :
        PropSPropRel (@SC.task_response_time_bound Task Job jaR costR jtR PR arrR schedR tsk rR)
          (I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
            Task dT Job dJ jaL costL jtL PL arrL schedL tsk rL).
      Proof.
        unfold SC.task_response_time_bound.
        cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frbf_job_of_task_related tsk j))|].
        unfold prosa.behavior.service.job_response_time_bound, prosa.behavior.service.completed_by.
        cbn [I.Prosa_Behavior_Service_job_response_time_bound I.Prosa_Behavior_Service_completed_by].
        exact (ar_bool_truth_correspondence _ _
          (svc_decide_le_related _ _ _ _ (Hcost j)
            (frbf_psr_service_related Job PR PL X schedR schedL Hs j _ _
              (svc_target_add_related _ _ _ _ (Hja j) Hr)))).
      Qed.

      Ltac frbf_patho_prefix :=
        apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|];
        apply ar_imp_correspondence;
          [exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr
            tsR tsL Hts maR maL Hma)|];
        apply (frbf_cover_pstate Job); let PR := fresh "PR" in let PL := fresh "PL" in
          let X := fresh "X" in intros PR PL X;
        apply (frbf_cover_psched Job PR PL X); let schedR := fresh "schedR" in
          let schedL := fresh "schedL" in let Hs := fresh "Hs" in intros schedR schedL Hs.

      Definition src_pathological_rbf_response_time_bound : Prop :=
        ltac:(body_of (fun s : S.statement_pathological_rbf_response_time_bound =>
          s Task tcR maR tsR Job jtR jaR costR arrR)).
      Definition tgt_pathological_rbf_response_time_bound : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_pathological_rbf_response_time_bound
          Task dT tcL maL tsL Job dJ jtL jaL costL arrL)).
      Theorem pathological_rbf_response_time_bound_correspondence :
        PropSPropRel src_pathological_rbf_response_time_bound tgt_pathological_rbf_response_time_bound.
      Proof.
        frbf_patho_prefix.
        apply ar_forall_identity_correspondence. intro tsk.
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
        apply ar_imp_correspondence;
          [exact (sub_nat_eq_correspondence _ _ _ _ (RBF maR maL Hma tsk _ _ (sub_nat_rel_canonical (S O)))
            (sub_nat_rel_canonical O))|].
        exact (frbf_task_response_time_bound_related PR PL X schedR schedL Hs tsk _ _ (sub_nat_rel_canonical O)).
      Qed.

      Definition src_pathological_total_hep_rbf_response_time_bound : Prop :=
        ltac:(body_of (fun s : S.statement_pathological_total_hep_rbf_response_time_bound =>
          s Task tcR maR tsR Job jtR jaR costR arrR)).
      Definition tgt_pathological_total_hep_rbf_response_time_bound : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_pathological_total_hep_rbf_response_time_bound
          Task dT tcL maL tsL Job dJ jtL jaL costL arrL)).
      Theorem pathological_total_hep_rbf_response_time_bound_correspondence :
        PropSPropRel src_pathological_total_hep_rbf_response_time_bound
          tgt_pathological_total_hep_rbf_response_time_bound.
      Proof.
        frbf_patho_prefix.
        apply cover_fp. intros fpR fpL Hfp.
        apply ar_imp_correspondence; [exact (frbf_reflexive_task_related fpR fpL Hfp)|].
        apply ar_forall_identity_correspondence. intro tsk.
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
        apply ar_imp_correspondence;
          [exact (sub_nat_eq_correspondence _ _ _ _
            (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
              fpR fpL Hfp tsk _ _ (sub_nat_rel_canonical (S O)))
            (sub_nat_rel_canonical O))|].
        exact (frbf_task_response_time_bound_related PR PL X schedR schedL Hs tsk _ _ (sub_nat_rel_canonical O)).
      Qed.

      Definition src_pathological_total_hep_rbf_any_bound : Prop :=
        ltac:(body_of (fun s : S.statement_pathological_total_hep_rbf_any_bound =>
          s Task tcR maR tsR Job jtR jaR costR arrR)).
      Definition tgt_pathological_total_hep_rbf_any_bound : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_pathological_total_hep_rbf_any_bound
          Task dT tcL maL tsL Job dJ jtL jaL costL arrL)).
      Theorem pathological_total_hep_rbf_any_bound_correspondence :
        PropSPropRel src_pathological_total_hep_rbf_any_bound tgt_pathological_total_hep_rbf_any_bound.
      Proof.
        frbf_patho_prefix.
        apply cover_fp. intros fpR fpL Hfp.
        apply ar_imp_correspondence; [exact (frbf_reflexive_task_related fpR fpL Hfp)|].
        apply ar_forall_identity_correspondence. intro tsk.
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
        apply ar_imp_correspondence;
          [exact (sub_nat_eq_correspondence _ _ _ _
            (total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
              fpR fpL Hfp tsk _ _ (sub_nat_rel_canonical (S O)))
            (sub_nat_rel_canonical O))|].
        apply ar_forall_nat_correspondence. intros rR rL Hr.
        exact (frbf_task_response_time_bound_related PR PL X schedR schedL Hs tsk _ _ Hr).
      Qed.
    End TS.
  End MA.

  (** *** Statements with the [MaxArrivals] instance after the task *)

  Ltac frbf_task_ma_prefix :=
    apply ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk;
    apply cover_ma; let maR := fresh "maR" in let maL := fresh "maL" in
      let Hma := fresh "Hma" in intros maR maL Hma.

  Definition src_task_rbf_0_zero : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_0_zero => s Task tcR)).
  Definition tgt_task_rbf_0_zero : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_0_zero Task dT tcL)).
  Theorem task_rbf_0_zero_correspondence : PropSPropRel src_task_rbf_0_zero tgt_task_rbf_0_zero.
  Proof.
    frbf_task_ma_prefix.
    apply ar_imp_correspondence; [exact (valid_arrival_curve_correspondence _ _ (Hma tsk))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (RBF maR maL Hma tsk _ _ (sub_nat_rel_canonical O))
      (sub_nat_rel_canonical O)).
  Qed.

  Definition src_task_rbf_monotone : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_monotone => s Task tcR)).
  Definition tgt_task_rbf_monotone : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_monotone Task dT tcL)).
  Theorem task_rbf_monotone_correspondence : PropSPropRel src_task_rbf_monotone tgt_task_rbf_monotone.
  Proof.
    frbf_task_ma_prefix.
    apply ar_imp_correspondence; [exact (valid_arrival_curve_correspondence _ _ (Hma tsk))|].
    apply frbf_monotone_related. intros dR dL Hd.
    exact (RBF maR maL Hma tsk _ _ Hd).
  Qed.

  Definition src_task_rbf_1_ge_task_cost : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_1_ge_task_cost => s Task tcR)).
  Definition tgt_task_rbf_1_ge_task_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_1_ge_task_cost Task dT tcL)).
  Theorem task_rbf_1_ge_task_cost_correspondence :
    PropSPropRel src_task_rbf_1_ge_task_cost tgt_task_rbf_1_ge_task_cost.
  Proof.
    frbf_task_ma_prefix.
    apply ar_imp_correspondence; [exact (frbf_max1_positive_related maR maL Hma tsk)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Htc tsk) (RBF maR maL Hma tsk _ _ (sub_nat_rel_canonical (S O)))).
  Qed.

  Definition src_task_rbf_ge_task_cost : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_ge_task_cost => s Task tcR)).
  Definition tgt_task_rbf_ge_task_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_ge_task_cost Task dT tcL)).
  Theorem task_rbf_ge_task_cost_correspondence :
    PropSPropRel src_task_rbf_ge_task_cost tgt_task_rbf_ge_task_cost.
  Proof.
    frbf_task_ma_prefix.
    apply ar_imp_correspondence; [exact (valid_arrival_curve_correspondence _ _ (Hma tsk))|].
    apply ar_imp_correspondence; [exact (frbf_max1_positive_related maR maL Hma tsk)|].
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ha)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Htc tsk) (RBF maR maL Hma tsk _ _ Ha)).
  Qed.

  Definition src_task_rbf_epsilon_gt_0 : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_epsilon_gt_0 => s Task tcR)).
  Definition tgt_task_rbf_epsilon_gt_0 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_epsilon_gt_0 Task dT tcL)).
  Theorem task_rbf_epsilon_gt_0_correspondence :
    PropSPropRel src_task_rbf_epsilon_gt_0 tgt_task_rbf_epsilon_gt_0.
  Proof.
    frbf_task_ma_prefix.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk))|].
    apply ar_imp_correspondence; [exact (frbf_max1_positive_related maR maL Hma tsk)|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (RBF maR maL Hma tsk _ _ (sub_nat_rel_canonical (S O)))).
  Qed.

  Definition src_task_cost_le_sum_rbf : Prop :=
    ltac:(body_of (fun s : S.statement_task_cost_le_sum_rbf => s Task tcR)).
  Definition tgt_task_cost_le_sum_rbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_cost_le_sum_rbf Task dT tcL)).
  Theorem task_cost_le_sum_rbf_correspondence :
    PropSPropRel src_task_cost_le_sum_rbf tgt_task_cost_le_sum_rbf.
  Proof.
    frbf_task_ma_prefix.
    apply ar_imp_correspondence; [exact (valid_arrival_curve_correspondence _ _ (Hma tsk))|].
    apply ar_imp_correspondence; [exact (frbf_max1_positive_related maR maL Hma tsk)|].
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ht)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Htc tsk)
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _ Ht)).
  Qed.

  (** *** Statements without a leading [MaxArrivals] instance *)

  Definition src_task_workload_between_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_task_workload_between_bounded => s Task tcR Job jtR costR arrR)).
  Definition tgt_task_workload_between_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_workload_between_bounded
      Task dT tcL Job dJ jtL costL arrL)).
  Theorem task_workload_between_bounded_correspondence :
    PropSPropRel src_task_workload_between_bounded tgt_task_workload_between_bounded.
  Proof.
    apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    exact (sub_nat_le_correspondence _ _ _ _
      (task_workload_between_correspondence Job costR costL Hcost arrR arrL Harr Task jtR jtL Hjt
        tsk _ _ _ _ H1 H2)
      (sub_mul_correspondence _ _ _ _ (Htc tsk)
        (number_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr
          tsk tsk _ _ _ _ (@Lean.eq_refl _ tsk) H1 H2))).
  Qed.

  Section OhepTS.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.
    Variable fpR : prosa.model.priority.definitions.FP_policy Task.
    Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
    Hypothesis Hfp : FrbfFPRel fpR fpL.

    Definition src_ohep_workload_le_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_ohep_workload_le_rbf => s Task tcR tsR fpR Job jtR costR arrR)).
    Definition tgt_ohep_workload_le_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_ohep_workload_le_rbf
        Task dT tcL tsL fpL Job dJ jtL costL arrL)).
    Theorem ohep_workload_le_rbf_correspondence :
      PropSPropRel src_ohep_workload_le_rbf tgt_ohep_workload_le_rbf.
    Proof.
      apply ar_imp_correspondence; [exact (frbf_all_jobs_from_taskset_related tsR tsL Hts)|].
      apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].
      apply cover_ma. intros maR maL Hma.
      apply ar_imp_correspondence;
        [exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr
          tsR tsL Hts maR maL Hma)|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frbf_job_of_task_related tsk j))|].
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (sub_nat_le_correspondence _ _ _ _
        (workload_of_jobs_correspondence Job costR costL Hcost _ _
          (fun x => wlb_another_task_hep_job_related Task Job jtR jtL Hjt _ _
            (frbf_hep_task_jobs fpR fpL Hfp) x j) _ _
          (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht
            (svc_target_add_related _ _ _ _ Ht Hd)))
        (total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fpR fpL Hfp tsk _ _ Hd)).
    Qed.
  End OhepTS.

  Ltac frbf_without_prefix :=
    apply ar_imp_correspondence;
      [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|];
    apply ar_imp_correspondence; [exact frbf_valid_job_costs_related|].

  Definition src_task_rbf_without_job_under_analysis_from_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_without_job_under_analysis_from_arrival =>
      s Task tcR Job jtR jaR costR arrR)).
  Definition tgt_task_rbf_without_job_under_analysis_from_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_without_job_under_analysis_from_arrival
      Task dT tcL Job dJ jtL jaL costL arrL)).
  Theorem task_rbf_without_job_under_analysis_from_arrival_correspondence :
    PropSPropRel src_task_rbf_without_job_under_analysis_from_arrival
      tgt_task_rbf_without_job_under_analysis_from_arrival.
  Proof.
    frbf_without_prefix.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frbf_job_of_task_related tsk j))|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have Hend := svc_target_add_related _ _ _ _ H1 Hd.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j) Hend)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (svc_target_sub_related _ _ _ _
        (task_workload_between_correspondence Job costR costL Hcost arrR arrL Harr Task jtR jtL Hjt
          tsk _ _ _ _ (Hja j) Hend)
        (Hcost j))
      (svc_target_sub_related _ _ _ _
        (sub_mul_correspondence _ _ _ _ (Htc tsk)
          (number_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr
            tsk tsk _ _ _ _ (@Lean.eq_refl _ tsk) (Hja j) Hend))
        (Htc tsk))).
  Qed.

  Definition src_task_rbf_without_job_under_analysis : Prop :=
    ltac:(body_of (fun s : S.statement_task_rbf_without_job_under_analysis =>
      s Task tcR Job jtR jaR costR arrR)).
  Definition tgt_task_rbf_without_job_under_analysis : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Rbf_task_rbf_without_job_under_analysis
      Task dT tcL Job dJ jtL jaL costL arrL)).
  Theorem task_rbf_without_job_under_analysis_correspondence :
    PropSPropRel src_task_rbf_without_job_under_analysis tgt_task_rbf_without_job_under_analysis.
  Proof.
    frbf_without_prefix.
    apply ar_forall_identity_correspondence. intro tsk.
    apply cover_ma. intros maR maL Hma.
    apply ar_imp_correspondence;
      [exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hma tsk))|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frbf_job_of_task_related tsk j))|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have Hend := svc_target_add_related _ _ _ _ H1 Hd.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j) Hend)|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 (Hja j))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (svc_target_sub_related _ _ _ _
        (task_workload_between_correspondence Job costR costL Hcost arrR arrL Harr Task jtR jtL Hjt
          tsk _ _ _ _ H1 Hend)
        (Hcost j))
      (svc_target_sub_related _ _ _ _ (RBF maR maL Hma tsk _ _ Hd) (Htc tsk))).
  Qed.
End Facts.
