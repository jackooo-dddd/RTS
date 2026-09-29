From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import ScheduleLimitedPreemptiveSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsElfLimitedPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedRtaRsElfLimitedPreemptive.
Module S := ScheduleLimitedPreemptiveSemanticSource.ScheduleLimitedPreemptiveSemanticSource.

(** Definition certificate for [model/schedule/limited_preemptive.v].

    Source side: the extracted byte-identical definition block; target side:
    the compiled Lean declaration.  Inputs: [JobPreemptable] by the accepted
    [PpJobPreemptableRel], processor states and schedules by the accepted
    two-sided [SvcProcessorStateRel]/[SvcScheduleRel], arrival sequences by
    [ArArrivalSequenceRel]; service and [scheduled_at] are related by the
    accepted [pp_service_related]/[pp_scheduled_at_related]. *)

Section Model.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jpR : prosa.PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem schedule_respects_preemption_model_correspondence :
    PropSPropRel (@S.schedule_respects_preemption_model Job PStateR jpR arrR schedR)
      (I.Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model
        Job dJ PStateL jpL arrL schedL).
  Proof.
    unfold S.schedule_respects_preemption_model.
    cbn [I.Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    have Hsvc := pp_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hjp j _ _ Hsvc))).
    - exact (ar_bool_truth_correspondence _ _
        (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
  Qed.
End Model.
