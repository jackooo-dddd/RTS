From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From prosa Require Import HyperperiodSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedHyperperiod ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskOffsetCorrespondence PeriodicCorrespondence
  NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence.

Module I := ImportedHyperperiod.
Module S := HyperperiodSemanticSource.HyperperiodSemanticSource.

(** Definition certificates for [analysis/definitions/hyperperiod.v]: for
    related task-offset, periodic-model, job-task and job-arrival instances,
    arrival sequences and task sets (the accepted relations, each with two-way
    totals), the seven extracted source definitions and the compiled Lean
    definitions are related.  Tasks and jobs are identity carriers; instants
    are related by [SubNatRel].  The hyperperiod goes through the accepted
    list-LCM correspondence, the arithmetic through the accepted Nat
    subtraction, multiplication, addition and division relations, the job
    lists through the accepted task-arrivals relation, and [index]/[nth]
    through the accepted [List.idxOf]/[List.getD] relations. *)

Section Hyperperiod.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Variable oR : TaskOffsetSemanticSource.TaskOffsetSemanticSource.TaskOffset Task.
  Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
  Hypothesis Hoff : OffRel Task oR oL.
  Variable pR : PeriodicSemanticSource.PeriodicSemanticSource.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel Task pR pL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Lemma hyp_period_map_canonical (xs : seq Task) :
    LcmoNatListRel (map (@PeriodicSemanticSource.PeriodicSemanticSource.task_period Task pR) xs)
      (I.List_map_inst2 Task Lean.Nat
        (I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task dT pL) (ar_list_to_imported xs)).
  Proof.
    induction xs as [|x xs IH].
    - exact (@Lean.eq_refl _ _).
    - cbn [map ar_list_to_imported].
      exact (sub_imported_eq_congr2 (I.List_cons_inst1 Lean.Nat) _ _ _ _ (Hp x) IH).
  Qed.

  Theorem hyperperiod_correspondence :
    SubNatRel (@S.hyperperiod Task pR tsR)
      (I.Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task dT pL tsL).
  Proof.
    unfold S.hyperperiod.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_hyperperiod].
    apply lcmo_lcml_correspondence.
    exact (sub_imported_eq_trans _ _ _ (hyp_period_map_canonical tsR)
      (sub_imported_eq_congr (I.List_map_inst2 Task Lean.Nat
        (I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task dT pL)) _ _ Hts)).
  Qed.

  Let Hmax := max_task_offset_correspondence Task oR oL Hoff tsR tsL Hts.

  Theorem hyperperiod_index_correspondence tR tL :
    SubNatRel tR tL ->
    SubNatRel (@S.hyperperiod_index Task oR pR tsR tR)
      (I.Prosa_Analysis_Definitions_Hyperperiod_hyperperiod_index Task dT oL pL tsL tL).
  Proof.
    intro Ht. unfold S.hyperperiod_index.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_hyperperiod_index].
    exact (lcmseqdm_div_correspondence _ _ _ _ (ari_nat_sub_related _ _ _ _ Ht Hmax)
      hyperperiod_correspondence).
  Qed.

  Theorem starting_instant_of_hyperperiod_correspondence tR tL :
    SubNatRel tR tL ->
    SubNatRel (@S.starting_instant_of_hyperperiod Task oR pR tsR tR)
      (I.Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_hyperperiod Task dT oL pL tsL tL).
  Proof.
    intro Ht. unfold S.starting_instant_of_hyperperiod.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_hyperperiod].
    exact (sub_add_correspondence _ _ _ _
      (lcmseqdm_mul_correspondence _ _ _ _ (hyperperiod_index_correspondence tR tL Ht)
        hyperperiod_correspondence) Hmax).
  Qed.

  Theorem starting_instant_of_corresponding_hyperperiod_correspondence (j : Job) :
    SubNatRel (@S.starting_instant_of_corresponding_hyperperiod Task oR pR Job jaR tsR j)
      (I.Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod
        Task dT oL pL Job dJ jaL tsL j).
  Proof.
    unfold S.starting_instant_of_corresponding_hyperperiod.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod].
    exact (starting_instant_of_hyperperiod_correspondence _ _ (Hja j)).
  Qed.

  Theorem jobs_in_hyperperiod_correspondence hR hL (tsk : Task) :
    SubNatRel hR hL ->
    ArListRel (@S.jobs_in_hyperperiod Task pR Job jtR tsR arrR hR tsk)
      (I.Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod
        Task dT pL Job dJ jtL tsL arrL hL tsk).
  Proof.
    intro Hh. unfold S.jobs_in_hyperperiod.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod].
    exact (task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _ _ _
      (@Lean.eq_refl _ _) Hh (sub_add_correspondence _ _ _ _ Hh hyperperiod_correspondence)).
  Qed.

  Theorem job_index_in_hyperperiod_correspondence (j : Job) hR hL (tsk : Task) :
    SubNatRel hR hL ->
    SubNatRel (@S.job_index_in_hyperperiod Task pR Job jtR tsR arrR j hR tsk)
      (I.Prosa_Analysis_Definitions_Hyperperiod_job_index_in_hyperperiod
        Task dT pL Job dJ jtL tsL arrL j hL tsk).
  Proof.
    intro Hh. unfold S.job_index_in_hyperperiod.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_job_index_in_hyperperiod].
    exact (ari_index_related Job j _ _ (jobs_in_hyperperiod_correspondence hR hL tsk Hh)).
  Qed.

  Theorem corresponding_job_in_hyperperiod_correspondence (j : Job) hR hL (tsk : Task) :
    SubNatRel hR hL ->
    Lean.eq (@S.corresponding_job_in_hyperperiod Task oR pR Job jtR jaR tsR arrR j hR tsk)
      (I.Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod
        Task dT oL pL Job dJ jtL jaL tsL arrL j hL tsk).
  Proof.
    intro Hh. unfold S.corresponding_job_in_hyperperiod.
    cbn [I.Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod].
    exact (ari_nth_related Job j _ _ _ _ (jobs_in_hyperperiod_correspondence hR hL tsk Hh)
      (job_index_in_hyperperiod_correspondence j _ _ tsk
        (starting_instant_of_corresponding_hyperperiod_correspondence j))).
  Qed.
End Hyperperiod.
