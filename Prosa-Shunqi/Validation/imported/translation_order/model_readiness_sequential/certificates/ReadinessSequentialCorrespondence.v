From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.readiness.sequential.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessSequential ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence.

Module I := ImportedReadinessSequential.

(** Certificates for the named source-local instance of
    [model/readiness/sequential.v]: for related inputs (task map, job
    arrival/cost, processor state, arrival sequence, schedule) the [job_ready]
    field of the source [sequential_ready_instance] and of the compiled Lean
    [sequential_ready_instance] are related, and the structure of the
    [ready_implies_pending] law statement is related.  Neither side's law
    proof is used. *)

Lemma rs_bool_implication_correspondence (aR bR : bool) (aL bL : I.Bool) :
  SvcBoolRel aR aL -> SvcBoolRel bR bL ->
  PropSPropRel (is_true aR -> is_true bR)
    (Lean.eq aL I.Bool_true -> Lean.eq bL I.Bool_true).
Proof.
  intros Ha Hb.
  destruct (svc_bool_truth_correspondence _ _ Ha) as [HaF HaB].
  destruct (svc_bool_truth_correspondence _ _ Hb) as [HbF HbB].
  apply prop_sprop_rel_intro.
  - intros Himp HaL. exact (HbF (Himp (HaB HaL))).
  - intro HimpL. apply strictly_inhabits.
    intro HaR. exact (HbB (HimpL (HaF HaR))).
Qed.

Section ReadinessSequential.
  Context (Job Task : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma rs_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
      (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [I.Prosa_Behavior_Service_pending].
    apply svc_bool_and_related.
    - exact (svc_has_arrived_related Job jaR jaL j Hja tR tL Ht).
    - exact (svc_bool_not_related _ _
        (sq_completed_by_related Job costR costL Hcost PStateR PStateL R
          schedR schedL Hsched j tR tL Ht)).
  Qed.

  Lemma rs_ready_field_source (j : Job) (tR : nat) :
    Logic.eq
      (@prosa.behavior.ready.job_ready Job PStateR costR jaR
        (@prosa.model.readiness.sequential.sequential_ready_instance
          Job Task jtR jaR costR PStateR arrR) schedR j tR)
      (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR &&
       @prosa.model.task.sequentiality.prior_jobs_complete
         Job Task jtR jaR costR PStateR arrR schedR j tR).
  Proof. exact Logic.eq_refl. Qed.

  Theorem sequential_ready_field_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.ready.job_ready Job PStateR costR jaR
        (@prosa.model.readiness.sequential.sequential_ready_instance
          Job Task jtR jaR costR PStateR arrR) schedR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL
        (I.Prosa_Model_Readiness_Sequential_sequential_ready_instance
          Job dJ Task dT jtL jaL costL PStateL arrL)
        schedL j tL).
  Proof.
    intro Ht.
    change (SvcBoolRel
      (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR &&
       @prosa.model.task.sequentiality.prior_jobs_complete
         Job Task jtR jaR costR PStateR arrR schedR j tR)
      (I.Bool_and
        (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL)
        (I.Prosa_Model_Task_Sequentiality_prior_jobs_complete
          Job dJ Task dT jtL jaL costL PStateL arrL schedL j tL))).
    apply svc_bool_and_related.
    - exact (rs_pending_related j tR tL Ht).
    - exact (prior_jobs_complete_correspondence Job Task jtR jtL Hjt jaR jaL Hja
        costR costL Hcost PStateR PStateL R arrR arrL Harr schedR schedL Hsched j tR tL Ht).
  Qed.

  Theorem sequential_ready_law_statement_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel
      (is_true (@prosa.behavior.ready.job_ready Job PStateR costR jaR
        (@prosa.model.readiness.sequential.sequential_ready_instance
          Job Task jtR jaR costR PStateR arrR) schedR j tR) ->
       is_true (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR))
      (Lean.eq
        (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL
          (I.Prosa_Model_Readiness_Sequential_sequential_ready_instance
            Job dJ Task dT jtL jaL costL PStateL arrL)
          schedL j tL) I.Bool_true ->
       Lean.eq (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL)
         I.Bool_true).
  Proof.
    intro Ht. apply rs_bool_implication_correspondence.
    - exact (sequential_ready_field_correspondence j tR tL Ht).
    - exact (rs_pending_related j tR tL Ht).
  Qed.
End ReadinessSequential.
