From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
Require Import OfficialCompletionSequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCompletionSequenceCombined
  ImportedSubadditivity.
From FoundationCertificates Require Import SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter
  ArrivalSequenceOperations ArrivalSequenceCorrespondence ServiceBaseAdapter
  ServiceScheduleOperations ServiceJobOperations ServiceCorrespondence.

(** Composition of the accepted arrivals_up_to, completes_at, and ordered
    filter correspondences, replayed against this exact combined import. *)
Section CompletionSequenceCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedCompletionSequenceCombined.Prosa_Behavior_Schedule_ProcessorState
      Job (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL :
    ImportedCompletionSequenceCombined.Prosa_Behavior_Schedule_schedule
      Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedCompletionSequenceCombined.Prosa_Behavior_Job_JobCost
    Job (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL :
    ImportedCompletionSequenceCombined.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (svc_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem completion_sequence_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@OfficialCompletionSequence.completion_sequence
        Job costR PStateR arrR schedR tR)
      (ImportedCompletionSequenceCombined.Prosa_Analysis_Definitions_CompletionSequence_completion_sequence
        Job (svc_decidable_eq Job) costL PStateL arrL schedL tL).
  Proof.
    intro Ht.
    unfold OfficialCompletionSequence.completion_sequence.
    cbn [ImportedCompletionSequenceCombined.Prosa_Analysis_Definitions_CompletionSequence_completion_sequence].
    apply ar_filter_related.
    - intro j.
      change (SvcBoolRel
        (@prosa.behavior.service.completes_at Job PStateR
          schedR costR j tR)
        (ImportedCompletionSequenceCombined.Prosa_Behavior_Service_completes_at
          Job (svc_decidable_eq Job) PStateL schedL costL j tL)).
      exact (completes_at_correspondence Job PStateR PStateL R
        schedR schedL Hsched costR costL Hcost j tR tL Ht).
    - exact (arrivals_up_to_correspondence_certificate
        Job arrR arrL Harr tR tL Ht).
  Qed.
End CompletionSequenceCorrespondence.

Print Assumptions completion_sequence_correspondence.
