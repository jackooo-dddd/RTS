From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import TaskIbfReadinessSemanticSource.
From prosa Require Import analysis.abstract.definitions analysis.definitions.readiness_interference
  model.job.properties model.processor.platform_properties model.processor.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskIbfReadiness ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers IdealAbstractRtaHelpers.
From FoundationCertificates Require
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence SequentialityCorrespondence
  IbfTaskHelpers IbfSupplyTaskCorrespondence ServiceInversionPredCorrespondence
  InterferenceCorrespondence ServiceOfJobsCorrespondence AbstractDefinitionsBusyInterval PriorityBaseAdapter
  ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence WorkloadBoundedCorrespondence.
From FoundationCertificates Require Import IbfTaskFullHelpers IwReadinessCorrespondence.

Module I := ImportedTaskIbfReadiness.
Module S := TaskIbfReadinessSemanticSource.TaskIbfReadinessSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module JSI := FoundationCertificates.JitterSvcIntervalOperations.
Module IBST := FoundationCertificates.IbfSupplyTaskCorrespondence.
Module WLB := FoundationCertificates.WorkloadBoundedCorrespondence.

(** Definition and statement correspondences for
    [analysis/abstract/restricted_supply/task_ibf_readiness.v].

    [task_intra_IBF]: the extracted byte-identical definition against the
    compiled Lean definition, its three bound functions related pointwise on
    related Nats.

    [instantiated_task_intra_interference_is_bounded]: the extracted statement
    specialised at its leading inputs (task and job types, [job_cost],
    [job_arrival], [job_task], a leading processor state) against the imported
    Lean theorem type.  Inputs: [job_cost], [job_arrival] pointwise; [job_task]
    by the accepted [AdJobTaskRel]; the processor state by the accepted
    two-sided [SvcProcessorStateRel] together with the pointwise [supply_on]
    relation.  JLFP policies (pointwise on Booleans), arrival sequences,
    schedules, tasks (identity) and the three bound functions (pointwise on
    related Nats) are covered in both directions.  The readiness instance is
    quantified before the policy, the arrival sequence and the schedule: the
    statement is first rewritten on both sides by a pure binder reordering
    (no extensionality) and the readiness instance is then covered at the
    statement's schedule pair by the accepted pair cover.  The source's
    section-local instances re-expose the accepted readiness-aware
    instantiation and are related by the accepted
    [rsi_interference_rel]/[rsi_workload_rel]; the readiness-aware
    service-inversion bound, the readiness-interference bound, the
    higher-or-equal-priority workload bound and the task intra-supply
    interference bound are the accepted definition certificates re-instantiated
    at this artifact.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** One-argument bound functions *)

Definition tibfr_fun1_to_target (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun xL => sub_nat_to_imported (fR (sub_nat_to_rocq xL)).
Definition tibfr_fun1_to_source (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun xR => sub_nat_to_rocq (fL (sub_nat_to_imported xR)).

Lemma tibfr_fun1_to_target_rel fR : JSI.SvcNatFunRel fR (tibfr_fun1_to_target fR).
Proof.
  intros xR xL Hx. unfold tibfr_fun1_to_target.
  rewrite (arta_nat_input _ _ Hx). exact (sub_nat_rel_canonical _).
Qed.

Lemma tibfr_fun1_to_source_rel fL : JSI.SvcNatFunRel (tibfr_fun1_to_source fL) fL.
Proof. intros xR xL Hx. destruct Hx. exact (sub_nat_imported_roundtrip _). Qed.

Lemma tibfr_forall_fun1 (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, JSI.SvcNatFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  exact (arta_forall_cover _ _ JSI.SvcNatFunRel tibfr_fun1_to_target tibfr_fun1_to_source
    tibfr_fun1_to_target_rel tibfr_fun1_to_source_rel PR PL).
Qed.

(** ** Binder reordering (both sides, no extensionality) *)

Lemma tibfr_reorder {JR JL PR PL AR AL SR SL : Type} (RR : PR -> Prop) (RL : PL -> SProp)
    (VR : AR -> Prop) (VL : AL -> SProp)
    (QR : JR -> PR -> AR -> SR -> Prop) (QL : JL -> PL -> AL -> SL -> SProp) :
  PropSPropRel (forall p, RR p -> forall a, VR a -> forall s (jr : JR), QR jr p a s)
    (forall p, RL p -> forall a, VL a -> forall s (jr : JL), QL jr p a s) ->
  PropSPropRel (forall (jr : JR) p, RR p -> forall a, VR a -> forall s, QR jr p a s)
    (forall (jr : JL) p, RL p -> forall a, VL a -> forall s, QL jr p a s).
Proof.
  intros [f g]. split.
  - intros HR jr p hr a hv s. exact (f (fun p hr a hv s jr => HR jr p hr a hv s) p hr a hv s jr).
  - intros HL jr p hr a hv s. exact (g (fun p hr a hv s jr => HL jr p hr a hv s) p hr a hv s jr).
Qed.

(** ** [task_intra_IBF] *)

Theorem task_intra_IBF_correspondence (SIR : nat -> nat) (SIL : Lean.Nat -> Lean.Nat)
    (HSI : JSI.SvcNatFunRel SIR SIL) (AWR : nat -> nat -> nat) (AWL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (HAW : ArtaFunRel AWR AWL) (RIR : nat -> nat -> nat) (RIL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (HRI : ArtaFunRel RIR RIL) (aR : nat) (aL : Lean.Nat) (rR : nat) (rL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel rR rL ->
  SubNatRel (@S.task_intra_IBF SIR AWR RIR aR rR)
    (I.Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF SIL AWL RIL aL rL).
Proof.
  intros Ha Hr. unfold S.task_intra_IBF.
  cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF].
  exact (svc_target_add_related _ _ _ _ (svc_target_add_related _ _ _ _ (HAW _ _ _ _ Ha Hr) (HSI _ _ Ha))
    (HRI _ _ _ _ Ha Hr)).
Qed.

Lemma tibfr_ibf_rel SIR SIL (HSI : JSI.SvcNatFunRel SIR SIL) AWR AWL (HAW : ArtaFunRel AWR AWL)
    RIR RIL (HRI : ArtaFunRel RIR RIL) :
  ArtaFunRel (@S.task_intra_IBF SIR AWR RIR)
    (I.Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF SIL AWL RIL).
Proof.
  intros aR aL rR rL Ha Hr. exact (task_intra_IBF_correspondence SIR SIL HSI AWR AWL HAW RIR RIL HRI _ _ _ _ Ha Hr).
Qed.

(** ** [instantiated_task_intra_interference_is_bounded] *)

Section TaskIntra.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Hypothesis Hsupply_on : forall sR sL cR,
    SSO.svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (SUP.supply_target_supply_on Job PStateL sL (SSO.svc_ps_core_to_target Job PStateR PStateL R cR)).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  Definition src_instantiated_task_intra_interference_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_task_intra_interference_is_bounded =>
      s Task Job costR jaR jtR PStateR)).
  Definition tgt_instantiated_task_intra_interference_is_bounded : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_instantiated_task_intra_interference_is_bounded
        Task dT Job dJ costL jaL jtL PStateL)).

  Theorem instantiated_task_intra_interference_is_bounded_correspondence :
    PropSPropRel src_instantiated_task_intra_interference_is_bounded
      tgt_instantiated_task_intra_interference_is_bounded.
  Proof.
    unfold src_instantiated_task_intra_interference_is_bounded, tgt_instantiated_task_intra_interference_is_bounded.
    imp (ibt_uni Job PStateR PStateL R).
    imp (rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on).
    imp (rsi_fully_consuming_rel Job PStateR PStateL R Hsupply_on).
    apply tibfr_reorder.
    apply (rsi_forall_jlfp Job). intros pR pL Hp.
    imp (rsi_reflexive_rel Job pR pL Hp).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    have HsJ := rsi_hs_jsvc Job PStateR PStateL R sR sL Hs.
    have HI := rsi_interference_rel Job PStateR PStateL R Hsupply_on jaR jaL costR costL sR sL Hs arrR arrL Harr
      jrR jrL Hjr pR pL Hp.
    have HW := rsi_workload_rel Job PStateR PStateL R Hsupply_on jaR jaL costR costL Hcost sR sL Hs arrR arrL Harr
      jrR jrL Hjr pR pL Hp.
    apply ad_forall_identity_correspondence. intro tsk.
    apply tibfr_forall_fun1. intros SIR SIL HSI.
    imp (FoundationCertificates.ReadinessAwareCorrespondence.service_inversion_is_bounded_correspondence
      Job PStateR PStateL R (rsi_jsvc Job PStateR PStateL R) sR sL Hs HsJ jaR jaL Hja costR costL Hcost
      jrR jrL Hjr arrR arrL Harr pR pL Hp _ _ HI _ _ HW SIR SIL HSI).
    apply arta_forall_fun. intros AWR AWL HAW.
    imp (WLB.athep_workload_is_bounded_correspondence Task Job costR costL Hcost jaR jaL Hja jtR jtL Hjt
      PStateR PStateL (rsi_jsvc Job PStateR PStateL R) pR pL Hp arrR arrL Harr sR sL HsJ tsk AWR AWL HAW).
    apply arta_forall_fun. intros RIR RIL HRI.
    imp (FoundationCertificates.ReadinessInterferenceCorrespondence.readiness_interference_is_bounded_correspondence
      Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost jrR jrL Hjr arrR arrL Harr pR pL Hp
      _ _ HI _ _ HW RIR RIL HRI).
    exact (IBST.task_intra_interference_is_bounded_by_correspondence Task Job PStateR PStateL R
      (rsi_sup Job PStateR PStateL R Hsupply_on) jtR jtL Hjt sR sL Hs (rsi_hs_sup Job PStateR PStateL R Hsupply_on sR sL Hs)
      arrR arrL Harr _ _ HI jaR jaL Hja costR costL Hcost _ _ HW
      _ _ (tibfr_ibf_rel SIR SIL HSI AWR AWL HAW RIR RIL HRI) tsk).
  Qed.
End TaskIntra.
