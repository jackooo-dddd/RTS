From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPreemptiveJobSemanticSource.
From prosa Require Import model.preemption.fully_preemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPreemptiveJob ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedFactsPreemptiveJob.
Module S := FactsPreemptiveJobSemanticSource.FactsPreemptiveJobSemanticSource.

(** Statement correspondences for [analysis/facts/preemption/job/preemptive.v].

    Source side: the extracted statements [S.statement_X] (elaborated with
    the source's section-local fully preemptive instance) specialised at
    their leading inputs; target side: the imported Lean theorem types, which
    pass the accepted Lean [fully_preemptive_job_model] explicitly.  The
    source instance (compiled from the pinned [fully_preemptive.v]) is
    related to the Lean definition as a [PpJobPreemptableRel].  Inputs:
    [job_cost] by [SvcJobCostRel], processor states and schedules by the
    accepted two-sided [SvcProcessorStateRel]/[SvcScheduleRel], arrival
    sequences by [ArArrivalSequenceRel].  Preemption validity and segment
    lengths are closed by the accepted [PreemptionParameterCorrespondence].
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section Preemptive.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Lemma fpj_fully_preemptive_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_preemptive.fully_preemptive_job_model Job)
      (I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job dJ).
  Proof. intros j nR nL Hn. exact (@Lean.eq_refl _ _). Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Let MAXNPS (j : Job) :=
    job_max_nonpreemptive_segment_correspondence Job costR costL Hcost _ _ fpj_fully_preemptive_related j.

  Definition src_job_max_nps_is_0 : Prop :=
    ltac:(body_of (fun s : S.statement_job_max_nps_is_0 => s Job costR)).
  Definition tgt_job_max_nps_is_0 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Preemptive_job_max_nps_is_0 Job dJ costL)).

  Theorem job_max_nps_is_0_correspondence :
    PropSPropRel src_job_max_nps_is_0 tgt_job_max_nps_is_0.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (Hcost j) (sub_nat_rel_canonical O))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (MAXNPS j) (sub_nat_rel_canonical O)).
  Qed.

  Definition src_job_max_nps_is_ε : Prop :=
    ltac:(body_of (fun s : S.statement_job_max_nps_is_ε => s Job costR)).
  Definition tgt_job_max_nps_is_ε : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Preemptive_job_max_nps_is__UU03b5_ Job dJ costL)).

  Theorem job_max_nps_is_ε_correspondence :
    PropSPropRel src_job_max_nps_is_ε tgt_job_max_nps_is_ε.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (MAXNPS j) (sub_nat_rel_canonical 1)).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition src_valid_fully_preemptive_model : Prop :=
    ltac:(body_of (fun s : S.statement_valid_fully_preemptive_model => s Job costR PStateR arrR schedR)).
  Definition tgt_valid_fully_preemptive_model : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Preemptive_valid_fully_preemptive_model
      Job dJ costL PStateL arrL schedL)).

  Theorem valid_fully_preemptive_model_correspondence :
    PropSPropRel src_valid_fully_preemptive_model tgt_valid_fully_preemptive_model.
  Proof.
    exact (valid_preemption_model_correspondence Job costR costL Hcost _ _ fpj_fully_preemptive_related
      PStateR PStateL R schedR schedL Hsched arrR arrL Harr).
  Qed.
End Preemptive.
