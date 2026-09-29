From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import ServiceInversionPredSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaPrmEdfFullyPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedRtaPrmEdfFullyPreemptive.
Module S := ServiceInversionPredSemanticSource.ServiceInversionPredSemanticSource.

(** Definition certificates for [analysis/definitions/service_inversion/pred.v].

    Source side: the extracted byte-identical definition blocks; target side:
    the compiled Lean declarations.  Inputs: processor states and schedules
    by the accepted two-sided [SvcProcessorStateRel]/[SvcScheduleRel],
    arrival sequences by [ArArrivalSequenceRel], the JLDP policy pointwise on
    Booleans, the interval predicate [P] pointwise by [PropSPropRel], the
    bound [B] pointwise by [SubNatRel], [job_arrival] by [ArJobArrivalRel],
    [job_cost] by [SvcJobCostRel], [job_task] by [Lean.eq].  [served_jobs_at]
    is replayed from the accepted interference certificate, [has] is related
    to [List.any] through kernel-checked Lean constructor equations, and the
    Boolean interval sum through the accepted [svc_interval_sum_related]
    against the kernel-guarded list-fold projection exported with the
    artifact. *)

Lemma sip_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma sip_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma sip_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply sip_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Lemma sip_bool_to_nat_related (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  intro Hb. unfold ArBoolRel in Hb.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr I.Bool_toNat _ _ Hb)).
  destruct bR; exact (@Lean.eq_refl _ _).
Qed.

Section Any.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

  Lemma sip_has_canonical (xs : seq X) :
    ArBoolRel (has PR xs) (I.List_any X (ar_list_to_imported xs) PL).
  Proof.
    induction xs as [|x xs IH].
    - exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ServiceInversionPredInterface_production_any_nil X PL)).
    - cbn [has ar_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ServiceInversionPredInterface_production_any_cons
          X PL x (ar_list_to_imported xs)))).
      exact (pp_bool_or_related _ _ _ _ (HP x) IH).
  Qed.

  Lemma sip_has_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (sip_has_canonical xsR)
      (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
  Qed.
End Any.

Section ServiceInversion.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable pR : prosa.model.priority.definitions.JLDP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ.
  Hypothesis Hp : forall tR tL, SubNatRel tR tL -> forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job_at Job pR tR x y)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ pL tL x y).

  Lemma sip_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma sip_receives_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_receives_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.receives_service_at.
    cbn [I.Prosa_Behavior_Service_receives_service_at].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (sip_service_at_related j tR tL Ht)).
  Qed.

  Lemma sip_served_jobs_at_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel (@prosa.analysis.definitions.service.served_jobs_at Job PStateR arrR schedR tR)
      (I.Prosa_Analysis_Definitions_Service_served_jobs_at Job dJ PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.service.served_jobs_at.
    cbn [I.Prosa_Analysis_Definitions_Service_served_jobs_at].
    apply ar_filter_related.
    - intro j. exact (sip_receives_service_at_related j tR tL Ht).
    - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
  Qed.

  Theorem service_inversion_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@S.service_inversion Job PStateR arrR schedR pR j tR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion
        Job dJ PStateL arrL schedL pL j tL).
  Proof.
    intro Ht. unfold S.service_inversion.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion].
    have Hs := sip_served_jobs_at_related tR tL Ht.
    apply ar_bool_and_related.
    - exact (svc_bool_not_related _ _ (ar_decide_mem_related Job j _ _ Hs)).
    - apply sip_has_related; [|exact Hs].
      intro jlp. exact (svc_bool_not_related _ _ (Hp tR tL Ht jlp j)).
  Qed.

  Theorem cumulative_service_inversion_correspondence (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@S.cumulative_service_inversion Job PStateR arrR schedR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion
        Job dJ PStateL arrL schedL pL j t1L t2L).
  Proof.
    intros H1 H2. unfold S.cumulative_service_inversion.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => nat_of_bool (@S.service_inversion Job PStateR arrR schedR pR j t))
      (fun t => I.Bool_toNat
        (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion
          Job dJ PStateL arrL schedL pL j t))
      H1 H2
      (fun a b Hab => sip_bool_to_nat_related _ _ (service_inversion_correspondence j a b Hab)).
    change (SubNatRel
      (\sum_(t1R <= t < t2R) nat_of_bool (@S.service_inversion Job PStateR arrR schedR pR j t))
      (I.Prosa_Validation_ServiceInversionPredInterface_cumulativeServiceInversionProjection
        Job dJ PStateL arrL schedL pL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable PR : Job -> nat -> nat -> Prop.
  Variable PL : Job -> Lean.Nat -> Lean.Nat -> SProp.
  Hypothesis HP : forall j t1R t1L t2R t2L, SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel (PR j t1R t2R) (PL j t1L t2L).

  Theorem pred_service_inversion_of_job_is_bounded_by_correspondence (j : Job) BR BL :
    SvcNatFunRel BR BL ->
    PropSPropRel (@S.pred_service_inversion_of_job_is_bounded_by Job jaR PStateR arrR schedR pR PR j BR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by
        Job dJ jaL PStateL arrL schedL pL PL j BL).
  Proof.
    intro HB. unfold S.pred_service_inversion_of_job_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence; [exact (HP j _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (cumulative_service_inversion_correspondence j _ _ _ _ H1 H2)
      (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) H1))).
  Qed.
End ServiceInversion.

Section TaskBound.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
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
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable pR : prosa.model.priority.definitions.JLDP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ.
  Hypothesis Hp : forall tR tL, SubNatRel tR tL -> forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job_at Job pR tR x y)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ pL tL x y).
  Variable PR : Job -> nat -> nat -> Prop.
  Variable PL : Job -> Lean.Nat -> Lean.Nat -> SProp.
  Hypothesis HP : forall j t1R t1L t2R t2L, SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel (PR j t1R t2R) (PL j t1L t2L).

  Lemma sip_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (sip_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (sip_decide_eq_related Task _ tsk).
  Qed.

  Theorem pred_service_inversion_is_bounded_by_correspondence (tsk : Task) BR BL :
    SvcNatFunRel BR BL ->
    PropSPropRel
      (@S.pred_service_inversion_is_bounded_by Task Job jtR jaR costR PStateR arrR schedR pR PR tsk BR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by
        Task dT Job dJ jtL jaL costL PStateL arrL schedL pL PL tsk BL).
  Proof.
    intro HB. unfold S.pred_service_inversion_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (sip_job_of_task_related tsk j))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    exact (pred_service_inversion_of_job_is_bounded_by_correspondence Job PStateR PStateL R
      schedR schedL Hsched arrR arrL Harr pR pL Hp jaR jaL Hja PR PL HP j BR BL HB).
  Qed.
End TaskBound.
