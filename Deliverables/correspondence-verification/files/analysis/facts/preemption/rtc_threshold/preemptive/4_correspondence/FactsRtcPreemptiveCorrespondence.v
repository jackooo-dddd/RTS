From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsRtcPreemptiveSemanticSource.
From prosa Require Import model.preemption.fully_preemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsRtcPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence TaskPreemptionFullyPreemptiveCorrespondence.

Module I := ImportedFactsRtcPreemptive.
Module S := FactsRtcPreemptiveSemanticSource.FactsRtcPreemptiveSemanticSource.

(** Statement correspondence for
    [analysis/facts/preemption/rtc_threshold/preemptive.v]: the extracted
    statement (elaborated with the source's section-local fully preemptive
    job, task and run-to-completion-threshold instances) against the
    imported Lean theorem type (which passes the accepted Lean definitions
    explicitly).  The job instance (compiled from the pinned
    [fully_preemptive.v]) is a [PpJobPreemptableRel] proved here, the
    threshold instance the accepted [tpfp_fully_preemptive_rtc_threshold_related];
    [arrivals_have_valid_job_costs] replays the accepted task-nonpreemptive
    proof and the task-level validity is closed by the accepted
    task-preemption-parameter certificate.  Inputs: [task_cost] pointwise by
    [SubNatRel], [job_task] by [Lean.eq], [job_cost] by [SvcJobCostRel],
    arrival sequences by [ArArrivalSequenceRel]; tasks and jobs are identity
    carriers.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma frp_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Section RtcPreemptive.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Lemma frp_fully_preemptive_job_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_preemptive.fully_preemptive_job_model Job)
      (I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job dJ).
  Proof. intros j nR nL Hn. exact (@Lean.eq_refl _ _). Qed.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma frp_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (frp_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma frp_valid_job_costs_related :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    unfold prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (frp_task_cost_of_job_related j))).
  Qed.

  Definition src_fully_preemptive_valid_task_run_to_completion_threshold : Prop :=
    ltac:(body_of (fun s : S.statement_fully_preemptive_valid_task_run_to_completion_threshold =>
      s Task tcR Job jtR costR arrR)).
  Definition tgt_fully_preemptive_valid_task_run_to_completion_threshold : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Preemptive_fully_preemptive_valid_task_run_to_completion_threshold
        Task dT tcL Job dJ jtL costL arrL)).
  Theorem fully_preemptive_valid_task_run_to_completion_threshold_correspondence :
    PropSPropRel src_fully_preemptive_valid_task_run_to_completion_threshold
      tgt_fully_preemptive_valid_task_run_to_completion_threshold.
  Proof.
    apply ar_imp_correspondence; [exact frp_valid_job_costs_related|].
    apply ar_forall_identity_correspondence. intro tsk.
    exact (valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc _ _
      (tpfp_fully_preemptive_rtc_threshold_related Task tcR tcL Htc) jtR jtL Hjt costR costL Hcost
      _ _ frp_fully_preemptive_job_related arrR arrL Harr tsk).
  Qed.
End RtcPreemptive.
