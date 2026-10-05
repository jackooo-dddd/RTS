From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import implementation.refinements.EDF.nonpreemptive_sched.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFNPSched ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  PsEac PsAb PsImplTask PsListOps PsSvcBase PsSvcNatBool PsSvcInterval PsSched.

Module I := ImportedRefEDFNPSched.
Module T := prosa.implementation.definitions.task.
Module S := prosa.implementation.refinements.EDF.nonpreemptive_sched.

(** Correspondences for [implementation/refinements/EDF/nonpreemptive_sched.v].

    Source side: the compiled official module; target side: the imported Lean declarations.  Concrete
    tasks and jobs are related by the accepted fieldwise canonical relations (two-way totals); arrival
    sequences and schedules by the job-relational relations of [PsSched].  The file's fixed instances
    are related directly: basic readiness by [pending], the fully-nonpreemptive model by its two
    equality tests on the service, and EDF (through the JLDP coercion and the job-deadline instance
    derived from the task deadline) by the deadline comparison.  Statement types are taken with
    [type of]; no source or target theorem is used. *)

Ltac type_of_term t := let T := type of t in exact T.

(** ** Principal types *)

Lemma Task_source_total (tR : S.Task) : ItTaskRel tR (it_task_export tR).
Proof. exact (concrete_task_source_total tR). Qed.

Lemma Task_target_total (tL : I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Task) :
  ItTaskRel (it_task_import tL) tL.
Proof. exact (concrete_task_target_total tL). Qed.

Lemma Job_source_total (jR : S.Job) : ItJobRel jR (it_job_export jR).
Proof. exact (concrete_job_source_total jR). Qed.

Lemma Job_target_total (jL : I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job) :
  ItJobRel (it_job_import jL) jL.
Proof. exact (concrete_job_target_total jL). Qed.

(** ** The fixed instances *)

Theorem basic_ready_instance_correspondence :
  ScReadyRel S.basic_ready_instance I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_basic_ready_instance.
Proof.
  intros sR sL Hs jR jL tR tL Hj Ht.
  exact (sc_pending_related _ _ Hs _ _ _ _ Hj Ht).
Qed.

Lemma ref_bool_or_related aR aL bR bL :
  SvcBoolRel aR aL -> SvcBoolRel bR bL -> SvcBoolRel (aR || bR) (I.Bool_or aL bL).
Proof.
  intros Ha Hb. destruct Ha. destruct Hb. destruct aR, bR; exact (@Lean.eq_refl _ _).
Qed.

Lemma ref_fully_nonpreemptive_related :
  ScPreemptRel (@prosa.model.preemption.fully_nonpreemptive.fully_nonpreemptive_job_model T.concrete_job T.JobCost)
    (I.Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model_inst1 LJ dJ jcL).
Proof.
  intros jR jL nR nL Hj Hn.
  exact (ref_bool_or_related _ _ _ _ (svc_decide_eq_related _ _ _ _ Hn (sub_nat_rel_canonical O))
    (svc_decide_eq_related _ _ _ _ Hn (it_job_cost _ _ Hj))).
Qed.

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
      I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job dJ) :
  JArrRel arrR arrL ->
  JSchedRel (S.sched arrR) (I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched arrL).
Proof.
  intro Harr. unfold S.sched.
  cbn [I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched].
  exact (sc_uni_schedule_related _ _ basic_ready_instance_correspondence _ _ ref_fully_nonpreemptive_related
    _ _ Harr _ _ ref_edf_related).
Qed.

(** ** Statements *)

Definition src_sched_jobs_must_be_ready_to_execute : Prop :=
  ltac:(type_of_term (@S.sched_jobs_must_be_ready_to_execute)).
Definition tgt_sched_jobs_must_be_ready_to_execute : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_jobs_must_be_ready_to_execute)).

Theorem sched_jobs_must_be_ready_to_execute_correspondence :
  PropSPropRel src_sched_jobs_must_be_ready_to_execute tgt_sched_jobs_must_be_ready_to_execute.
Proof.
  unfold src_sched_jobs_must_be_ready_to_execute, tgt_sched_jobs_must_be_ready_to_execute.
  apply sc_forall_arr. intros arrR arrL Harr.
  exact (sc_must_be_ready_related _ _ basic_ready_instance_correspondence _ _ (sched_correspondence _ _ Harr)).
Qed.

Definition src_sched_valid : Prop := ltac:(type_of_term (@S.sched_valid)).
Definition tgt_sched_valid : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_valid)).

Theorem sched_valid_correspondence : PropSPropRel src_sched_valid tgt_sched_valid.
Proof.
  unfold src_sched_valid, tgt_sched_valid.
  apply sc_forall_arr. intros arrR arrL Harr.
  exact (sc_valid_schedule_related _ _ basic_ready_instance_correspondence _ _ Harr _ _
    (sched_correspondence _ _ Harr)).
Qed.

(** The step of non-preemption: one schedule, related instants [t] and [t + 1]. *)
Lemma ref_np_step (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) jR jL tR tL tR' tL' :
  ItJobRel jR jL -> SubNatRel tR tL -> SubNatRel tR' tL' ->
  PropSPropRel
    (prosa.behavior.service.scheduled_at sR jR tR ->
     ~~ prosa.behavior.service.completed_by sR jR tR' -> prosa.behavior.service.scheduled_at sR jR tR')
    (Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst7 LJ dJ PSL sL jL tL) I.Bool_true ->
     Lean.eq (I.Bool_not (I.Prosa_Behavior_Service_completed_by_inst7 LJ dJ PSL sL jcL jL tL')) I.Bool_true ->
     Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst7 LJ dJ PSL sL jL tL') I.Bool_true).
Proof.
  intros Hj Ht Ht'.
  apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_scheduled_at_related _ _ Hs _ _ _ _ Hj Ht)).
  apply sc_imp; first exact (svc_bool_truth_correspondence _ _
    (svc_bool_not_related _ _ (sc_completed_by_related _ _ Hs _ _ _ _ Hj Ht'))).
  exact (svc_bool_truth_correspondence _ _ (sc_scheduled_at_related _ _ Hs _ _ _ _ Hj Ht')).
Qed.

Definition src_sched_nonpreemptive_next : Prop := ltac:(type_of_term (@S.sched_nonpreemptive_next)).
Definition tgt_sched_nonpreemptive_next : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_nonpreemptive_next)).

Theorem sched_nonpreemptive_next_correspondence :
  PropSPropRel src_sched_nonpreemptive_next tgt_sched_nonpreemptive_next.
Proof.
  unfold src_sched_nonpreemptive_next, tgt_sched_nonpreemptive_next.
  apply sc_forall_arr. intros arrR arrL Harr.
  apply sc_forall_job. intros jR jL Hj.
  apply sc_forall_nat. intros tR tL Ht.
  exact (ref_np_step _ _ (sched_correspondence _ _ Harr) _ _ _ _ _ _ Hj Ht (sc_succ_related _ _ Ht)).
Qed.

Definition src_sched_nonpreemptive : Prop := ltac:(type_of_term (@S.sched_nonpreemptive)).
Definition tgt_sched_nonpreemptive : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_nonpreemptive)).

Theorem sched_nonpreemptive_correspondence :
  PropSPropRel src_sched_nonpreemptive tgt_sched_nonpreemptive.
Proof.
  unfold src_sched_nonpreemptive, tgt_sched_nonpreemptive.
  apply sc_forall_arr. intros arrR arrL Harr.
  have Hs := sched_correspondence _ _ Harr.
  unfold S.sched in Hs. cbn [I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched] in Hs.
  unfold prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.
  cbn [I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst7].
  apply sc_forall_job. intros jR jL Hj.
  apply sc_forall_nat. intros tR tL Ht.
  apply sc_forall_nat. intros tR' tL' Ht'.
  apply sc_imp; first exact (svc_target_le_related _ _ _ _ Ht Ht').
  exact (ref_np_step _ _ Hs _ _ _ _ _ _ Hj Ht Ht').
Qed.

Definition src_respects_policy_at_preemption_point_edf_np : Prop :=
  ltac:(type_of_term (@S.respects_policy_at_preemption_point_edf_np)).
Definition tgt_respects_policy_at_preemption_point_edf_np : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_respects_policy_at_preemption_point_edf_np)).

Theorem respects_policy_at_preemption_point_edf_np_correspondence :
  PropSPropRel src_respects_policy_at_preemption_point_edf_np tgt_respects_policy_at_preemption_point_edf_np.
Proof.
  unfold src_respects_policy_at_preemption_point_edf_np, tgt_respects_policy_at_preemption_point_edf_np.
  apply sc_forall_arr. intros arrR arrL Harr.
  apply sc_imp; first exact (sc_valid_arrival_sequence_related _ _ Harr).
  unfold prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point.
  cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst7].
  exact (sc_respects_JLDP_related _ _ basic_ready_instance_correspondence _ _ ref_fully_nonpreemptive_related
    _ _ Harr _ _ (sched_correspondence _ _ Harr) _ _ ref_edf_related).
Qed.
