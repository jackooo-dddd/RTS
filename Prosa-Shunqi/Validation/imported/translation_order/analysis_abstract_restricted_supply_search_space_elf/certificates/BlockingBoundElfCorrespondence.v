From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import BlockingBoundElfSemanticSource.
From prosa Require Import util.int model.priority.gel model.priority.elf model.task.arrival.curves.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpaceElf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers.

Module I := ImportedSearchSpaceElf.
Module S := BlockingBoundElfSemanticSource.BlockingBoundElfSemanticSource.
Module T := prosa.TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

Import GRing.Theory Num.Theory.

(** Definition certificate for [analysis/definitions/blocking_bound/elf.v].

    Source side: the extracted byte-identical definition block (with its
    section [Let]s); target side: the compiled Lean declaration.  Inputs:
    task costs, maximum nonpreemptive segments (the accepted
    [TppMaxSegmentRel]), arrival curves and the FP policy pointwise; priority
    points by the accepted [GelPriorityPointRel]; task sets by [ArListRel];
    durations by [SubNatRel].  MathComp's conditional [\max] big operator is
    related to [bigMaxListCond] through the accepted kernel-checked Lean
    constructor equations (replayed from the accepted FP blocking-bound
    certificate); [hp_task]/[ep_task] through the Boolean connectives; the
    strict integer comparison [A%:R + pp tsk < pp tsk_o] is rewritten to
    [(A + 1)%:R + pp tsk <= pp tsk_o] on both sides (MathComp [lezD1] on
    the source side, a kernel-checked Lean equation exported with the
    artifact on the target side) and related by the accepted GEL helpers. *)

(** ** Conditional maximum over a sequence (replayed from the accepted FP certificate) *)

Section BigMax.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).
  Variable FR : X -> nat.
  Variable FL : X -> Lean.Nat.
  Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

  Lemma bbelf_bigmax_canonical (xs : seq X) :
    SubNatRel (\max_(x <- xs | PR x) FR x)
      (I.Prosa_Util_Minmax_bigMaxListCond X (ar_list_to_imported xs) PL FL).
  Proof.
    induction xs as [|x xs IH].
    - rewrite big_nil.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_nil X PL FL)).
    - rewrite big_cons. cbn [ar_list_to_imported].
      have Hx := HP x. unfold ArBoolRel in Hx.
      destruct (PR x).
      + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_true
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
        refine (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _ (pp_max_canonical (FR x) (\max_(y <- xs | PR y) FR y))) _).
        exact (sub_imported_eq_congr2 I.Nat_max _ _ _ _ (HF x) IH).
      + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_false
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
  Qed.

  Lemma bbelf_bigmax_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\max_(x <- xsR | PR x) FR x) (I.Prosa_Util_Minmax_bigMaxListCond X xsL PL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (bbelf_bigmax_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Minmax_bigMaxListCond X l PL FL) _ _ Hxs)).
  Qed.
End BigMax.

(** ** Definition *)

Section Blocking.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable mR : T.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Lemma bbelf_hp_task_related (x y : Task) :
    PdBoolRel (@prosa.model.priority.definitions.hp_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.hp_task. cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp x y) (pd_bool_not_related _ _ (Hfp y x))).
  Qed.

  Lemma bbelf_ep_task_related (x y : Task) :
    PdBoolRel (@prosa.model.priority.definitions.ep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task. cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp x y) (Hfp y x)).
  Qed.

  Lemma bbelf_point_lt_related (tsk tsk_o : Task) (AR : nat) (AL : Lean.Nat) (HA : SubNatRel AR AL)
      (bL : I.Bool)
      (Hg : Lean.eq bL (gel_target_int_le
        (gel_target_add (svc_target_add AL (sub_nat_to_imported 1))
          (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL tsk))
        (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL tsk_o))) :
    PdBoolRel ((AR%:R + @prosa.model.priority.gel.task_priority_point Task ppR tsk)
        < @prosa.model.priority.gel.task_priority_point Task ppR tsk_o)%R bL.
  Proof.
    have E : ((AR%:R + @prosa.model.priority.gel.task_priority_point Task ppR tsk)
        < @prosa.model.priority.gel.task_priority_point Task ppR tsk_o)%R
      = ((((AR + 1)%:R : int) + @prosa.model.priority.gel.task_priority_point Task ppR tsk)
        <= @prosa.model.priority.gel.task_priority_point Task ppR tsk_o)%R.
    { by rewrite -lezD1 natrD addrAC. }
    rewrite E. unfold PdBoolRel.
    refine (sub_imported_eq_trans _ _ _
      (gel_le_related _ _ _ _
        (gel_add_related _ _ _ _ (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical 1)) (Hpp tsk))
        (Hpp tsk_o)) _).
    exact (sub_imported_eq_sym _ _ Hg).
  Qed.

  Theorem blocking_bound_correspondence (tsk : Task) (AR : nat) (AL : Lean.Nat) (HA : SubNatRel AR AL) :
    SubNatRel (@S.blocking_bound Task tcR mR ppR tsR maR fpR tsk AR)
      (I.Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound Task dT tcL mL ppL tsL maL fpL tsk AL).
  Proof.
    unfold S.blocking_bound. cbv zeta.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound].
    apply bbelf_bigmax_related; [| |exact Hts].
    - intro tsk_o.
      exact (pd_bool_or_related _ _ _ _
        (pd_bool_and_related _ _ _ _ (bbelf_hp_task_related tsk tsk_o) (pd_bool_and_related _ _ _ _
          (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hma tsk_o _ _ (sub_nat_rel_canonical 1)))
          (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Htc tsk_o))))
        (pd_bool_and_related _ _ _ _
          (pd_bool_and_related _ _ _ _ (bbelf_ep_task_related tsk tsk_o)
            (bbelf_point_lt_related tsk tsk_o AR AL HA _
              (I.Prosa_Validation_BlockingBoundElfInterface_production_int_add_lt_iff AL _ _)))
          (pd_bool_and_related _ _ _ _
          (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hma tsk_o _ _ (sub_nat_rel_canonical 1)))
          (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Htc tsk_o))))).
    - intro tsk_o.
      exact (svc_target_sub_related _ _ _ _ (Hm tsk_o) (sub_nat_rel_canonical 1)).
  Qed.
End Blocking.
