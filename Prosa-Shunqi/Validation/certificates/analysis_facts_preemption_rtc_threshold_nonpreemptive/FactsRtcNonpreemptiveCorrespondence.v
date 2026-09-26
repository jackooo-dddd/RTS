From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsRtcNonpreemptiveSemanticSource.
From prosa Require Import model.schedule.nonpreemptive model.preemption.fully_nonpreemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsRtcNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence TaskPreemptionFullyNonpreemptiveCorrespondence.

Module I := ImportedFactsRtcNonpreemptive.
Module S := FactsRtcNonpreemptiveSemanticSource.FactsRtcNonpreemptiveSemanticSource.
Module T := TaskPreemptionFullyNonpreemptiveSemanticSource.TaskPreemptionFullyNonpreemptiveSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma frnp_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Section Fnp.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Lemma frnp_fully_nonpreemptive_job_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_nonpreemptive.fully_nonpreemptive_job_model Job costR)
      (I.Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job dJ costL).
  Proof.
    intros j nR nL Hn.
    exact (pp_bool_or_related _ _ _ _
      (pp_nat_eqb_related _ _ _ _ Hn (sub_nat_rel_canonical O))
      (pp_nat_eqb_related _ _ _ _ Hn (Hcost j))).
  Qed.
End Fnp.


(** Statement correspondences for [analysis/facts/preemption/rtc_threshold/nonpreemptive.v]:
    the extracted statements (elaborated with the source's section-local
    fully nonpreemptive job and run-to-completion-threshold instances)
    against the imported Lean theorem types (which pass the accepted Lean
    definitions explicitly).  The job instance is a [PpJobPreemptableRel]
    proved above, the threshold instance the accepted
    [tpfn_fully_nonpreemptive_rtc_threshold_related]; [job_rtct] and the
    task-level validity are closed by the accepted preemption-parameter and
    task-preemption-parameter certificates.  No source or target theorem is
    used. *)

Section RtcNonpreemptive.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Let FNPJ := frnp_fully_nonpreemptive_job_related Job costR costL Hcost.
  Let RTCT := job_rtct_correspondence Job costR costL Hcost _ _ FNPJ.

  Definition src_job_rtc_threshold_is_0 : Prop :=
    ltac:(body_of (fun s : S.statement_job_rtc_threshold_is_0 => s Job costR)).
  Definition tgt_job_rtc_threshold_is_0 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Nonpreemptive_job_rtc_threshold_is_0
      Job dJ costL)).
  Theorem job_rtc_threshold_is_0_correspondence :
    PropSPropRel src_job_rtc_threshold_is_0 tgt_job_rtc_threshold_is_0.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (Hcost j) (sub_nat_rel_canonical O))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (RTCT j) (sub_nat_rel_canonical O)).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition src_job_rtc_threshold_is_ε : Prop :=
    ltac:(body_of (fun s : S.statement_job_rtc_threshold_is_ε => s Job costR arrR)).
  Definition tgt_job_rtc_threshold_is_ε : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Nonpreemptive_job_rtc_threshold_is__UU03b5_
      Job dJ costL arrL)).
  Theorem job_rtc_threshold_is_ε_correspondence :
    PropSPropRel src_job_rtc_threshold_is_ε tgt_job_rtc_threshold_is_ε.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (RTCT j) (sub_nat_rel_canonical 1)).
  Qed.

  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
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

  Definition src_fully_nonpreemptive_valid_task_run_to_completion_threshold : Prop :=
    ltac:(body_of (fun s : S.statement_fully_nonpreemptive_valid_task_run_to_completion_threshold =>
      s Task tcR Job jtR costR arrR)).
  Definition tgt_fully_nonpreemptive_valid_task_run_to_completion_threshold : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_Nonpreemptive_fully_nonpreemptive_valid_task_run_to_completion_threshold
        Task dT tcL Job dJ jtL costL arrL)).
  Theorem fully_nonpreemptive_valid_task_run_to_completion_threshold_correspondence :
    PropSPropRel src_fully_nonpreemptive_valid_task_run_to_completion_threshold
      tgt_fully_nonpreemptive_valid_task_run_to_completion_threshold.
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk))|].
    exact (valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc _ _
      (tpfn_fully_nonpreemptive_rtc_threshold_related Task) jtR jtL Hjt costR costL Hcost
      _ _ FNPJ arrR arrL Harr tsk).
  Qed.
End RtcNonpreemptive.
