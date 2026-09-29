From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import SbfBusySemanticSource analysis.definitions.sbf.pred.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaPrmEdfFullyPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  BusyIntervalClassicalHelpers.
From FoundationCertificates Require
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  PredHelpers.

Module I := ImportedRtaPrmEdfFullyPreemptive.
Module S := SbfBusySemanticSource.SbfBusySemanticSource.
Module BIC := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.
Module PC := FoundationCertificates.PredHelpers.
Module SSO := FoundationCertificates.SupplyScheduleOperations.
Module ASO := FoundationCertificates.ArrivalSequenceOperations.

(** Definition certificates for [analysis/definitions/sbf/busy.v].

    Both definitions instantiate the accepted [pred_sbf_respected] /
    [valid_pred_sbf] certificates of the [sbf/pred] (Supply) family, whose
    predicate parameter is related pointwise, with the source-local predicate
    [bi_prefix_of_tsk := fun j t1 t2 => job_of_task tsk j /\ busy_interval_prefix
    arr_seq sched j t1 t2].  That predicate relation is proved here from the
    accepted classical [busy_interval_prefix] certificate (ArrivalsSeq /
    JitterSvc family) and a [job_of_task] relation re-proved from the task
    field relation; nothing is assumed about the predicate.  As in the
    accepted abstract [busy_sbf] certificate, the processor-state pair is
    related by both accepted two-sided relations: the supply observation
    ([SupplyProcessorStateRel]) and the scheduled/service observation
    ([SvcProcessorStateRel]), with schedules related through each.  The
    arrival-sequence relation of the Supply family is the same relation as
    the ArrivalsSeq one (re-stated per family, identical definitions), and is
    obtained from it by conversion.  No source or target theorem is used. *)

Section SbfBusy.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.

  Variable Rsupply : SSO.SupplyProcessorStateRel Job PStateR PStateL.
  Variable Rservice : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis HschedSupply : SSO.SupplyScheduleRel Job PStateR PStateL Rsupply schedR schedL.
  Hypothesis HschedService : SvcScheduleRel Job PStateR PStateL Rservice schedR schedL.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : BicJLFPRel Job pR pL.

  Variable tsk : Task.

  Lemma sbfb_task_eq_bool_related (x y : Task) :
    ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (dT x y)).
  Proof.
    apply ar_decide_bool_correspondence.
    apply prop_sprop_rel_intro.
    - move/eqP => Heq. exact (coq_eq_to_imported_eq x y Heq).
    - intro Heq. apply strictly_inhabits. apply/eqP.
      exact (imported_eq_to_coq_eq x y Heq).
  Qed.

  Lemma sbfb_job_of_task_related (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    exact (sub_imported_eq_trans _ _ _
      (sbfb_task_eq_bool_related (@prosa.model.task.concept.job_task Job Task jtR j) tsk)
      (sub_imported_eq_congr (fun t => I.Decidable_decide (Lean.eq t tsk) (dT t tsk)) _ _ (Hjt j))).
  Qed.

  Definition sbfb_predR (j : Job) (t1 t2 : nat) : Prop :=
    is_true (@prosa.model.task.concept.job_of_task Job Task jtR tsk j) /\
    @BIC.busy_interval_prefix Job jaR costR PStateR arrR schedR pR j t1 t2.

  Definition sbfb_predL (j : Job) (t1 t2 : Lean.Nat) : SProp :=
    And
      (Lean.eq (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j) I.Bool_true)
      (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
        Job dJ jaL costL PStateL arrL schedL pL j t1 t2).

  Lemma sbfb_pred_related : PC.PredPredicateRel Job sbfb_predR sbfb_predL.
  Proof.
    intros j t1R t1L t2R t2L Ht1 Ht2.
    apply ar_and_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (sbfb_job_of_task_related j)).
    - exact (busy_interval_prefix_correspondence Job jaR jaL Hja costR costL Hcost
        PStateR PStateL Rservice arrR arrL Harr schedR schedL HschedService pR pL Hp
        j t1R t1L t2R t2L Ht1 Ht2).
  Qed.

  Lemma sbfb_arrival_sequence_rel : ASO.ArArrivalSequenceRel Job arrR arrL.
  Proof. exact Harr. Qed.

  Variable fR : nat -> nat.
  Variable fL : Lean.Nat -> Lean.Nat.
  Hypothesis Hf : PC.PredFunctionRel fR fL.

  Theorem sbf_respected_in_busy_interval_correspondence :
    PropSPropRel
      (@S.sbf_respected_in_busy_interval Task Job jaR costR jtR PStateR arrR schedR pR tsk fR)
      (I.Prosa_Analysis_Definitions_Sbf_Busy_sbf_respected_in_busy_interval
        Task dT Job dJ jaL costL jtL PStateL arrL schedL pL tsk fL).
  Proof.
    exact (PC.pred_sbf_respected_correspondence Job PStateR PStateL Rsupply
      schedR schedL HschedSupply arrR arrL sbfb_arrival_sequence_rel sbfb_predR sbfb_predL
      sbfb_pred_related fR fL Hf).
  Qed.

  Theorem valid_busy_sbf_correspondence :
    PropSPropRel
      (@S.valid_busy_sbf Task Job jaR costR jtR PStateR arrR schedR pR tsk fR)
      (I.Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf
        Task dT Job dJ jaL costL jtL PStateL arrL schedL pL tsk fL).
  Proof.
    exact (PC.pred_valid_pred_sbf_correspondence Job PStateR PStateL Rsupply
      schedR schedL HschedSupply arrR arrL sbfb_arrival_sequence_rel sbfb_predR sbfb_predL
      sbfb_pred_related fR fL Hf).
  Qed.
End SbfBusy.
