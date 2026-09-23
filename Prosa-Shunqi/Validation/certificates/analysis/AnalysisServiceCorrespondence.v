From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAnalysisService ImportedSubadditivity.
From FoundationCertificates Require Import SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations
  ArrivalSequenceCorrespondence ServiceBaseAdapter
  ServiceScheduleOperations ServiceJobOperations ServiceCorrespondence.

(** The option bridge is value-level and reusable for any imported List/Option
    with the same constructors and head computation. It does not posit the
    conclusion as a semantic hypothesis. *)
Definition as_option_to_imported {T : Type} (o : option T) :
    ImportedAnalysisService.Option T :=
  match o with
  | None => ImportedAnalysisService.Option_none T
  | Some x => ImportedAnalysisService.Option_some T x
  end.

Definition AsOptionRel {T : Type} (oR : option T)
    (oL : ImportedAnalysisService.Option T) : SProp :=
  Lean.eq (as_option_to_imported oR) oL.

Lemma as_ohead_correspondence {T : Type}
    (xsR : seq T) (xsL : ImportedAnalysisService.List T) :
  ArListRel xsR xsL ->
  AsOptionRel (ohead xsR) (ImportedAnalysisService.List_head__q T xsL).
Proof.
  intro Hxs. unfold AsOptionRel, ArListRel in *.
  refine (sub_imported_eq_trans _ _ _ _
    (sub_imported_eq_congr (ImportedAnalysisService.List_head__q T) _ _ Hxs)).
  destruct xsR as [|x xs]; cbn [ohead ar_list_to_imported as_option_to_imported
    ImportedAnalysisService.List_head__q
    ImportedAnalysisService.List_getLast__q_match_1];
    exact (@Lean.eq_refl _ _).
Qed.

Section ServedAtCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedAnalysisService.Prosa_Behavior_Schedule_ProcessorState
      Job (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL :
    ImportedAnalysisService.Prosa_Behavior_Schedule_schedule
      Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL :
    ImportedAnalysisService.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (svc_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem served_jobs_at_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.analysis.definitions.service.served_jobs_at
        Job PStateR arrR schedR tR)
      (ImportedAnalysisService.Prosa_Analysis_Definitions_Service_served_jobs_at
        Job (svc_decidable_eq Job) PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.service.served_jobs_at.
    cbn [ImportedAnalysisService.Prosa_Analysis_Definitions_Service_served_jobs_at].
    apply ar_filter_related.
    - intro j.
      change (SvcBoolRel
        (@prosa.behavior.service.receives_service_at Job PStateR
          schedR j tR)
        (ImportedAnalysisService.Prosa_Behavior_Service_receives_service_at
          Job (svc_decidable_eq Job) PStateL schedL j tL)).
      exact (receives_service_at_correspondence
        Job PStateR PStateL R schedR schedL Hsched j tR tL Ht).
    - exact (arrivals_up_to_correspondence_certificate
        Job arrR arrL Harr tR tL Ht).
  Qed.

  Theorem served_job_at_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    AsOptionRel
      (@prosa.analysis.definitions.service.served_job_at
        Job PStateR arrR schedR tR)
      (ImportedAnalysisService.Prosa_Analysis_Definitions_Service_served_job_at
        Job (svc_decidable_eq Job) PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.service.served_job_at.
    cbn [ImportedAnalysisService.Prosa_Analysis_Definitions_Service_served_job_at].
    apply as_ohead_correspondence.
    exact (served_jobs_at_correspondence tR tL Ht).
  Qed.
End ServedAtCorrespondence.

Print Assumptions as_ohead_correspondence.
Print Assumptions served_jobs_at_correspondence.
Print Assumptions served_job_at_correspondence.
