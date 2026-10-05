From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsModelSequentialSemanticSource.
From prosa Require Import model.readiness.sequential analysis.definitions.readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsModelSequential ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence
  ReadinessCorrespondence FactsReadinessSequentialHelpers.

Module I := ImportedFactsModelSequential.
Module S := FactsModelSequentialSemanticSource.FactsModelSequentialSemanticSource.
Module FRS := FactsReadinessSequentialSemanticSource.FactsReadinessSequentialSemanticSource.

(** Statement correspondences for [analysis/facts/model/sequential.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job and task types, the job-task, arrival and cost
    classes, the processor model, the arrival sequence and, where leading,
    the schedule); target side: the imported Lean theorem types.  Inputs:
    [job_task] by [Lean.eq], [job_arrival] by [ArJobArrivalRel], [job_cost]
    by [SvcJobCostRel], processor states by the accepted two-sided
    [SvcProcessorStateRel], schedules by [SvcScheduleRel], arrival sequences
    by [ArArrivalSequenceRel]; jobs identity, instants by [SubNatRel].
    [sequential_tasks], [same_task], [completed_by] and [scheduled_at] are
    closed by the accepted sequentiality certificate.

    [sequential_tasks_from_readiness] quantifies a readiness instance [JR]
    (followed by [sequential_readiness JR] and, after a schedule binder, by
    [valid_schedule] under [JR]).  The two statements are related without
    relating arbitrary instances: in each direction the other side's
    statement is instantiated at the canonical sequential readiness instance
    (pendency conjoined with [prior_jobs_complete], the accepted
    [sequential_readiness_instance] of each side, related by the accepted
    [frs_sequential_instance_related]); the canonical instance satisfies
    [sequential_readiness] by construction, and every schedule valid under an
    instance satisfying [sequential_readiness] is valid under the canonical
    instance (ready jobs are pending by the class law, and have their prior
    jobs complete by [sequential_readiness]).  The canonical statements are
    related over the accepted schedule cover.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fms_and_true_intro (a b : I.Bool) :
  Lean.eq a I.Bool_true -> Lean.eq b I.Bool_true -> Lean.eq (I.Bool_and a b) I.Bool_true.
Proof.
  destruct a; cbn; intros Ha Hb.
  - exact (ar_false_elim _ (ar_false_ne_true Ha)).
  - exact Hb.
Qed.

Lemma fms_and_true_right (a b : I.Bool) :
  Lean.eq (I.Bool_and a b) I.Bool_true -> Lean.eq b I.Bool_true.
Proof.
  destruct a; cbn; intro H.
  - exact (ar_false_elim _ (ar_false_ne_true H)).
  - exact H.
Qed.

Section Sequential.
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

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Let SEQ := sequential_tasks_correspondence Job Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
      PStateR PStateL R arrR arrL Harr schedR schedL Hsched.
    Let SAME := sq_same_task_related Job Task jtR jtL Hjt.
    Let COMPL := sq_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.
    Let SCHED := sq_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched.

    Definition src_scheduler_executes_job_with_earliest_arrival : Prop :=
      ltac:(body_of (fun s : S.statement_scheduler_executes_job_with_earliest_arrival =>
        s Job Task jtR jaR costR PStateR arrR schedR)).
    Definition tgt_scheduler_executes_job_with_earliest_arrival : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Model_Sequential_scheduler_executes_job_with_earliest_arrival
          Job dJ Task dT jtL jaL costL PStateL arrL schedL)).

    Theorem scheduler_executes_job_with_earliest_arrival_correspondence :
      PropSPropRel src_scheduler_executes_job_with_earliest_arrival
        tgt_scheduler_executes_job_with_earliest_arrival.
    Proof.
      unfold src_scheduler_executes_job_with_earliest_arrival,
        tgt_scheduler_executes_job_with_earliest_arrival.
      imp SEQ.
      apply ar_forall_identity_correspondence => j1.
      apply ar_forall_identity_correspondence => j2.
      apply ar_forall_nat_correspondence => tR tL Ht.
      imp (arrives_in_correspondence_certificate Job arrR arrL j1 Harr).
      imp (arrives_in_correspondence_certificate Job arrR arrL j2 Harr).
      imp (ar_bool_truth_correspondence _ _ (SAME j1 j2)).
      imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (COMPL j2 tR tL Ht))).
      imp (ar_bool_truth_correspondence _ _ (SCHED j1 tR tL Ht)).
      exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2)).
    Qed.

    Definition src_sequential_tasks_different_tasks : Prop :=
      ltac:(body_of (fun s : S.statement_sequential_tasks_different_tasks =>
        s Job Task jtR jaR costR PStateR arrR schedR)).
    Definition tgt_sequential_tasks_different_tasks : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Model_Sequential_sequential_tasks_different_tasks
          Job dJ Task dT jtL jaL costL PStateL arrL schedL)).

    Theorem sequential_tasks_different_tasks_correspondence :
      PropSPropRel src_sequential_tasks_different_tasks tgt_sequential_tasks_different_tasks.
    Proof.
      unfold src_sequential_tasks_different_tasks, tgt_sequential_tasks_different_tasks.
      imp SEQ.
      apply ar_forall_identity_correspondence => j1.
      apply ar_forall_identity_correspondence => j2.
      apply ar_forall_nat_correspondence => tR tL Ht.
      imp (arrives_in_correspondence_certificate Job arrR arrL j1 Harr).
      imp (arrives_in_correspondence_certificate Job arrR arrL j2 Harr).
      imp (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2)).
      imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (COMPL j1 tR tL Ht))).
      imp (ar_bool_truth_correspondence _ _ (SCHED j2 tR tL Ht)).
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (SAME j1 j2))).
    Qed.
  End Sched.

  (** ** Readiness quantified inside [sequential_tasks_from_readiness] *)

  Let canonR := @FRS.sequential_readiness_instance Job Task jtR jaR costR PStateR arrR.
  Let canonL := I.Prosa_Analysis_Facts_Readiness_Sequential_sequential_readiness_instance
    Job dJ Task dT jtL jaL costL PStateL arrL.
  Let READY := frs_sequential_instance_related Job Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
    PStateR PStateL R arrR arrL Harr.

  (** The statement at the canonical instances (the accepted proof of the
      readiness-sequential certificate, over the accepted schedule cover). *)
  Lemma fms_canonical_rel :
    PropSPropRel
      (forall schedR, @prosa.behavior.ready.valid_schedule Job jaR PStateR schedR costR canonR arrR ->
        @prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PStateR arrR schedR)
      (forall schedL, I.Prosa_Behavior_Ready_valid_schedule Job dJ jaL PStateL schedL costL canonL arrL ->
        I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task dT jtL jaL costL PStateL arrL schedL).
  Proof.
    apply (frs_forall_schedule Job PStateR PStateL R). intros schedR schedL Hf.
    have Hsched := rd_schedule_fun_to_svc Job PStateR PStateL R schedR schedL Hf.
    apply ar_imp_correspondence.
    - unfold prosa.behavior.ready.valid_schedule.
      cbn [I.Prosa_Behavior_Ready_valid_schedule].
      apply ar_and_correspondence.
      + unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
        cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        imp (svc_bool_truth_correspondence _ _
          (sq_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
        exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      + unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
        cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        imp (svc_bool_truth_correspondence _ _
          (sq_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
        exact (svc_bool_truth_correspondence _ _ (READY schedR schedL Hsched j tR tL Ht)).
    - exact (sequential_tasks_correspondence Job Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
        PStateR PStateL R arrR arrL Harr schedR schedL Hsched).
  Qed.

  Definition src_sequential_tasks_from_readiness : Prop :=
    ltac:(body_of (fun s : S.statement_sequential_tasks_from_readiness =>
      s Job Task jtR jaR costR PStateR arrR)).
  Definition tgt_sequential_tasks_from_readiness : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sequential_sequential_tasks_from_readiness
      Job dJ Task dT jtL jaL costL PStateL arrL)).

  Theorem sequential_tasks_from_readiness_correspondence :
    PropSPropRel src_sequential_tasks_from_readiness tgt_sequential_tasks_from_readiness.
  Proof.
    unfold src_sequential_tasks_from_readiness, tgt_sequential_tasks_from_readiness.
    imp (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply prop_sprop_rel_intro.
    - (* source statement => target statement *)
      intros HR JL HseqL schedL HvL.
      have HRc := HR canonR ltac:(move=> s j t H; case/andP: H => _ H; exact H).
      have HLc := prop_to_sprop _ _ fms_canonical_rel HRc.
      destruct HvL as [Hc Hm].
      refine (HLc schedL (And_intro _ _ Hc (fun j t Hs => _))).
      have Hr := Hm j t Hs.
      exact (fms_and_true_intro _ _
        (I.Prosa_Behavior_Ready_JobReady_ready_implies_pending Job dJ PStateL costL jaL JL schedL j t Hr)
        (HseqL schedL j t Hr)).
    - (* target statement => source statement *)
      intro HL. apply strictly_inhabits.
      have HLc := HL canonL (fun s j t H => fms_and_true_right _ _ H).
      have HRc := sprop_to_prop _ _ fms_canonical_rel HLc.
      intros [f Hf] HseqR schedR [Hc Hm].
      apply: HRc. split; [exact Hc|].
      move=> j t Hs. have Hr := Hm j t Hs.
      rewrite /canonR /FRS.sequential_readiness_instance /prosa.behavior.ready.job_ready /=.
      apply/andP. split; [exact (Hf _ _ _ Hr) | exact (HseqR _ _ _ Hr)].
  Qed.
End Sequential.
