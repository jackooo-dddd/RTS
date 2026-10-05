From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import implementation.refinements.EDF.preemptive_sched.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFPSched ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  PsEac PsAb PsImplTask PsListOps PsSvcBase PsSvcNatBool PsSvcInterval PsSched.

Module I := ImportedRefEDFPSched.
Module T := prosa.implementation.definitions.task.
Module S := prosa.implementation.refinements.EDF.preemptive_sched.

(** Correspondences for [implementation/refinements/EDF/preemptive_sched.v].

    Source side: the compiled official module; target side: the imported Lean declarations.  Concrete
    tasks and jobs are related by the accepted fieldwise canonical relations (two-way totals); arrival
    sequences and schedules by the job-relational relations of [PsSched].  The file's fixed instances
    are related directly: basic readiness by [pending], the fully-preemptive model (always preemptable)
    by its constant, and EDF (through the JLDP coercion and the job-deadline instance derived from the
    task deadline) by the deadline comparison.  Statement types are taken with [type of]; no source or
    target theorem is used. *)

Ltac type_of_term t := let T := type of t in exact T.

(** ** Principal types *)

Lemma Task_source_total (tR : S.Task) : ItTaskRel tR (it_task_export tR).
Proof. exact (concrete_task_source_total tR). Qed.

Lemma Task_target_total (tL : I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_Task) :
  ItTaskRel (it_task_import tL) tL.
Proof. exact (concrete_task_target_total tL). Qed.

Lemma Job_source_total (jR : S.Job) : ItJobRel jR (it_job_export jR).
Proof. exact (concrete_job_source_total jR). Qed.

Lemma Job_target_total (jL : I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job) :
  ItJobRel (it_job_import jL) jL.
Proof. exact (concrete_job_target_total jL). Qed.

(** ** The fixed instances *)

Theorem basic_ready_instance_correspondence :
  ScReadyRel S.basic_ready_instance I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_basic_ready_instance.
Proof.
  intros sR sL Hs jR jL tR tL Hj Ht.
  exact (sc_pending_related _ _ Hs _ _ _ _ Hj Ht).
Qed.

Lemma ref_fully_preemptive_related :
  ScPreemptRel (@prosa.model.preemption.fully_preemptive.fully_preemptive_job_model T.concrete_job)
    (I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model_inst1 LJ dJ).
Proof. intros jR jL nR nL Hj Hn. exact (@Lean.eq_refl _ _). Qed.

Lemma ref_job_deadline_related (jR : T.concrete_job) jL : ItJobRel jR jL ->
  SubNatRel (@prosa.behavior.job.job_deadline T.concrete_job
      (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline T.concrete_job T.concrete_task
        T.TaskDeadline T.JobArrival T.JobTask) jR)
    (I.Prosa_Behavior_Job_JobDeadline_job_deadline_inst1 LJ dJ
      (I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline_inst3 LJ LT dJ dT
        I.Prosa_Implementation_Definitions_Task_TaskDeadline jaL I.Prosa_Implementation_Definitions_Task_JobTask) jL).
Proof.
  intro Hj.
  exact (sub_add_correspondence _ _ _ _ (it_job_arrival _ _ Hj) (it_task_deadline _ _ (it_job_task _ _ Hj))).
Qed.

Lemma ref_edf_related :
  ScPolicyRel
    (@prosa.model.priority.coercion.JLFP_to_JLDP T.concrete_job
      (@prosa.model.priority.edf.EDF T.concrete_job
        (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline T.concrete_job T.concrete_task
          T.TaskDeadline T.JobArrival T.JobTask)))
    (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP_inst1 LJ dJ
      (I.Prosa_Model_Priority_Edf_EDF_inst1 LJ dJ
        (I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline_inst3 LJ LT dJ dT
          I.Prosa_Implementation_Definitions_Task_TaskDeadline jaL I.Prosa_Implementation_Definitions_Task_JobTask))).
Proof.
  intros tR tL Ht xR xL yR yL Hx Hy.
  exact (svc_decide_le_related _ _ _ _ (ref_job_deadline_related _ _ Hx) (ref_job_deadline_related _ _ Hy)).
Qed.

(** ** The schedule *)

Theorem sched_correspondence (arrR : prosa.behavior.arrival_sequence.arrival_sequence S.Job)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
      I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job dJ) :
  JArrRel arrR arrL ->
  JSchedRel (S.sched arrR) (I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_sched arrL).
Proof.
  intro Harr. unfold S.sched.
  cbn [I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_sched].
  exact (sc_uni_schedule_related _ _ basic_ready_instance_correspondence _ _ ref_fully_preemptive_related
    _ _ Harr _ _ ref_edf_related).
Qed.

(** ** Statements *)

Definition src_sched_valid : Prop := ltac:(type_of_term (@S.sched_valid)).
Definition tgt_sched_valid : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_sched_valid)).

Theorem sched_valid_correspondence : PropSPropRel src_sched_valid tgt_sched_valid.
Proof.
  unfold src_sched_valid, tgt_sched_valid.
  apply sc_forall_arr. intros arrR arrL Harr.
  exact (sc_valid_schedule_related _ _ basic_ready_instance_correspondence _ _ Harr _ _
    (sched_correspondence _ _ Harr)).
Qed.

Definition src_respects_policy_at_preemption_point_edf_fp : Prop :=
  ltac:(type_of_term (@S.respects_policy_at_preemption_point_edf_fp)).
Definition tgt_respects_policy_at_preemption_point_edf_fp : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_PreemptiveSched_respects_policy_at_preemption_point_edf_fp)).

Theorem respects_policy_at_preemption_point_edf_fp_correspondence :
  PropSPropRel src_respects_policy_at_preemption_point_edf_fp tgt_respects_policy_at_preemption_point_edf_fp.
Proof.
  unfold src_respects_policy_at_preemption_point_edf_fp, tgt_respects_policy_at_preemption_point_edf_fp.
  apply sc_forall_arr. intros arrR arrL Harr.
  apply sc_imp; first exact (sc_valid_arrival_sequence_related _ _ Harr).
  unfold prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point.
  cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst7].
  exact (sc_respects_JLDP_related _ _ basic_ready_instance_correspondence _ _ ref_fully_preemptive_related
    _ _ Harr _ _ (sched_correspondence _ _ Harr) _ _ ref_edf_related).
Qed.
