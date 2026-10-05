From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import implementation.refinements.FP.preemptive_sched.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefFPPSched ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  PsEac PsAb PsImplTask PsListOps PsSvcBase PsSvcNatBool PsSvcInterval PsSched.

Module I := ImportedRefFPPSched.
Module T := prosa.implementation.definitions.task.
Module S := prosa.implementation.refinements.FP.preemptive_sched.

(** Correspondences for [implementation/refinements/FP/preemptive_sched.v].

    Source side: the compiled official module; target side: the imported Lean declarations.  Concrete
    tasks and jobs are related by the accepted fieldwise canonical relations (two-way totals); arrival
    sequences and schedules by the job-relational relations of [PsSched].  The file's fixed instances
    are related directly: sequential readiness (for related arrival sequences) by [pending] and the
    completion of the earlier jobs of the same task, the fully-preemptive model (always preemptable) by
    its constant, and [NumericFPAscending] (through the FP-to-JLFP and JLDP coercions) by the comparison
    of the task priorities.  Statement types are taken with [type of]; no source or target theorem is
    used. *)

Ltac type_of_term t := let T := type of t in exact T.

(** ** Principal types *)

Lemma Task_source_total (tR : S.Task) : ItTaskRel tR (it_task_export tR).
Proof. exact (concrete_task_source_total tR). Qed.

Lemma Task_target_total (tL : I.Prosa_Implementation_Refinements_FP_PreemptiveSched_Task) :
  ItTaskRel (it_task_import tL) tL.
Proof. exact (concrete_task_target_total tL). Qed.

Lemma Job_source_total (jR : S.Job) : ItJobRel jR (it_job_export jR).
Proof. exact (concrete_job_source_total jR). Qed.

Lemma Job_target_total (jL : I.Prosa_Implementation_Refinements_FP_PreemptiveSched_Job) :
  ItJobRel (it_job_import jL) jL.
Proof. exact (concrete_job_target_total jL). Qed.

(** ** Sequential readiness *)

Lemma ref_all_related (pR : T.concrete_job -> bool) (pL : LJ -> I.Bool) xsR xsL :
  (forall jR jL, ItJobRel jR jL -> SvcBoolRel (pR jR) (pL jL)) -> JListRel xsR xsL ->
  SvcBoolRel (all pR xsR) (I.List_all_inst1 LJ xsL pL).
Proof.
  intros Hp Hxs. unfold JListRel, ArListRel in Hxs. destruct Hxs.
  induction xsR as [|x xs IH]; first exact (@Lean.eq_refl _ _).
  exact (svc_bool_and_related _ _ _ _ (Hp x _ (@Lean.eq_refl _ _)) IH).
Qed.

Lemma ref_job_of_task_related (tR : T.concrete_task) tL (jR : T.concrete_job) jL :
  ItTaskRel tR tL -> ItJobRel jR jL ->
  SvcBoolRel (@prosa.model.task.concept.job_of_task T.concrete_job T.concrete_task T.JobTask tR jR)
    (I.Prosa_Model_Task_Concept_job_of_task_inst3 LJ dJ LT dT I.Prosa_Implementation_Definitions_Task_JobTask tL jL).
Proof. intros Ht Hj. exact (it_task_decide_related _ _ _ _ (it_job_task _ _ Hj) Ht). Qed.

Lemma ref_task_arrivals_between_related (arrR : ArrR) (arrL : ArrL) (Harr : JArrRel arrR arrL)
    (tR : T.concrete_task) tL t1R t1L t2R t2L :
  ItTaskRel tR tL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  JListRel (@prosa.model.task.arrivals.task_arrivals_between T.concrete_job T.concrete_task T.JobTask arrR tR t1R t2R)
    (I.Prosa_Model_Task_Arrivals_task_arrivals_between_inst3 LJ dJ LT dT I.Prosa_Implementation_Definitions_Task_JobTask
      arrL tL t1L t2L).
Proof.
  intros Ht H1 H2.
  exact (sc_filter_related _ _ _ _ (fun jR jL Hj => ref_job_of_task_related _ _ _ _ Ht Hj)
    (sc_arrivals_between_related _ _ Harr _ _ _ _ H1 H2)).
Qed.

Theorem sequential_ready_instance_correspondence (arrR : prosa.behavior.arrival_sequence.arrival_sequence S.Job)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
      I.Prosa_Implementation_Refinements_FP_PreemptiveSched_Job dJ) :
  JArrRel arrR arrL ->
  ScReadyRel (S.sequential_ready_instance arrR)
    (I.Prosa_Implementation_Refinements_FP_PreemptiveSched_sequential_ready_instance arrL).
Proof.
  intros Harr sR sL Hs jR jL tR tL Hj Ht.
  exact (svc_bool_and_related _ _ _ _ (sc_pending_related _ _ Hs _ _ _ _ Hj Ht)
    (ref_all_related _ _ _ _ (fun xR xL Hx => sc_completed_by_related _ _ Hs _ _ _ _ Hx Ht)
      (ref_task_arrivals_between_related _ _ Harr _ _ _ _ _ _ (it_job_task _ _ Hj) (sub_nat_rel_canonical O)
        (it_job_arrival _ _ Hj)))).
Qed.

(** ** The preemption model and the policy *)

Lemma ref_fully_preemptive_related :
  ScPreemptRel (@prosa.model.preemption.fully_preemptive.fully_preemptive_job_model T.concrete_job)
    (I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model_inst1 LJ dJ).
Proof. intros jR jL nR nL Hj Hn. exact (@Lean.eq_refl _ _). Qed.

Lemma ref_fp_related :
  ScPolicyRel
    (@prosa.model.priority.coercion.JLFP_to_JLDP T.concrete_job
      (@prosa.model.priority.coercion.FP_to_JLFP T.concrete_job T.concrete_task T.JobTask
        (@prosa.model.priority.numeric_fixed_priority.NumericFPAscending T.concrete_task T.TaskPriority)))
    (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP_inst1 LJ dJ
      (I.Prosa_Model_Priority_Coercion_FP_to_JLFP_inst3 LJ dJ LT dT I.Prosa_Implementation_Definitions_Task_JobTask
        (I.Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1 LT dT
          I.Prosa_Implementation_Definitions_Task_TaskPriority))).
Proof.
  intros tR tL Ht xR xL yR yL Hx Hy.
  exact (svc_decide_le_related _ _ _ _ (it_task_priority _ _ (it_job_task _ _ Hy))
    (it_task_priority _ _ (it_job_task _ _ Hx))).
Qed.

(** ** The schedule *)

Theorem sched_correspondence (arrR : prosa.behavior.arrival_sequence.arrival_sequence S.Job)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
      I.Prosa_Implementation_Refinements_FP_PreemptiveSched_Job dJ) :
  JArrRel arrR arrL ->
  JSchedRel (S.sched arrR) (I.Prosa_Implementation_Refinements_FP_PreemptiveSched_sched arrL).
Proof.
  intro Harr. unfold S.sched.
  cbn [I.Prosa_Implementation_Refinements_FP_PreemptiveSched_sched].
  exact (sc_uni_schedule_related _ _ (sequential_ready_instance_correspondence _ _ Harr) _ _
    ref_fully_preemptive_related _ _ Harr _ _ ref_fp_related).
Qed.

(** ** Statements *)

Definition src_sched_valid : Prop := ltac:(type_of_term (@S.sched_valid)).
Definition tgt_sched_valid : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_FP_PreemptiveSched_sched_valid)).

Theorem sched_valid_correspondence : PropSPropRel src_sched_valid tgt_sched_valid.
Proof.
  unfold src_sched_valid, tgt_sched_valid.
  apply sc_forall_arr. intros arrR arrL Harr.
  exact (sc_valid_schedule_related _ _ (sequential_ready_instance_correspondence _ _ Harr) _ _ Harr _ _
    (sched_correspondence _ _ Harr)).
Qed.

Definition src_respects_policy_at_preemption_point : Prop :=
  ltac:(type_of_term (@S.respects_policy_at_preemption_point)).
Definition tgt_respects_policy_at_preemption_point : SProp :=
  ltac:(type_of_term (@I.Prosa_Implementation_Refinements_FP_PreemptiveSched_respects_policy_at_preemption_point)).

Theorem respects_policy_at_preemption_point_correspondence :
  PropSPropRel src_respects_policy_at_preemption_point tgt_respects_policy_at_preemption_point.
Proof.
  unfold src_respects_policy_at_preemption_point, tgt_respects_policy_at_preemption_point.
  apply sc_forall_arr. intros arrR arrL Harr.
  apply sc_imp; first exact (sc_valid_arrival_sequence_related _ _ Harr).
  unfold prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point.
  cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst15].
  exact (sc_respects_JLDP_related _ _ (sequential_ready_instance_correspondence _ _ Harr) _ _
    ref_fully_preemptive_related _ _ Harr _ _ (sched_correspondence _ _ Harr) _ _ ref_fp_related).
Qed.
