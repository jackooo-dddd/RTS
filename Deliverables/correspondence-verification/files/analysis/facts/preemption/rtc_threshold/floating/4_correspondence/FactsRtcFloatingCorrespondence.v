From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsRtcFloatingSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsRtcFloating ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence
  TaskPreemptionParametersCorrespondence TaskFloatingNonpreemptiveCorrespondence.

Module I := ImportedFactsRtcFloating.
Module S := FactsRtcFloatingSemanticSource.FactsRtcFloatingSemanticSource.
Module LP := LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module TP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := prosa.PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma rtc_lean_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

(** Statement correspondence for [analysis/facts/preemption/rtc_threshold/floating.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, task cost, job-task, job cost and preemption
    classes, arrival sequence); target side: the imported Lean theorem type.
    Inputs: [task_cost], [job_cost] pointwise by [SubNatRel], [job_task] by
    [Lean.eq], [JobPreemptable] by the accepted [PpJobPreemptableRel],
    arrival sequences by [ArArrivalSequenceRel]; tasks identity.  The
    section-local [floating_preemptive_rtc_threshold] is related by the
    accepted [tfn_floating_preemptive_rtc_threshold_related], the valid
    run-to-completion threshold by the accepted task-preemption-parameters
    certificate; valid job costs are related here pointwise.  No source or
    target theorem is used. *)

Section RtcFloating.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
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

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

  Lemma frf_valid_job_costs_rel :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence => j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    unfold prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_bool_truth_correspondence.
    refine (rtc_lean_transport (fun v => SvcBoolRel _ (I.Decidable_decide _ (I.Nat_decLe _ (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)))) _ _ (Hjt j) _).
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (Htc _)).
  Qed.

  Definition src_floating_preemptive_valid_task_run_to_completion_threshold : Prop :=
    ltac:(body_of (fun s : S.statement_floating_preemptive_valid_task_run_to_completion_threshold =>
      s Task tcR Job jtR costR jpR arrR)).
  Definition tgt_floating_preemptive_valid_task_run_to_completion_threshold : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Floating_floating_preemptive_valid_task_run_to_completion_threshold
      Job dJ Task dT tcL jtL costL jpL arrL)).

  Theorem floating_preemptive_valid_task_run_to_completion_threshold_correspondence :
    PropSPropRel src_floating_preemptive_valid_task_run_to_completion_threshold
      tgt_floating_preemptive_valid_task_run_to_completion_threshold.
  Proof.
    unfold src_floating_preemptive_valid_task_run_to_completion_threshold,
      tgt_floating_preemptive_valid_task_run_to_completion_threshold.
    imp frf_valid_job_costs_rel.
    apply ar_forall_identity_correspondence => tsk.
    exact (valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc _ _
      (tfn_floating_preemptive_rtc_threshold_related Task tcR tcL Htc) jtR jtL Hjt costR costL Hcost
      jpR jpL Hjp arrR arrL Harr tsk).
  Qed.
End RtcFloating.
