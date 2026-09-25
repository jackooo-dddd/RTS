From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.definitions.task_schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskSchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations
  ServiceBaseAdapter ServiceNatBoolOperations ServiceIntervalOperations
  ServiceScheduleOperations.

(** The only class premise is the ordinary fieldwise JobTask representation
    relation.  It has a canonical import witness below. *)
Definition TsJobTaskRel (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedTaskSchedule.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
      (ImportedTaskSchedule.Prosa_Model_Task_Concept_JobTask_job_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j).

Definition ts_import_job_task (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
    ImportedTaskSchedule.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) :=
  ImportedTaskSchedule.Prosa_Model_Task_Concept_JobTask_mk
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jobTaskR j).

Lemma ts_job_task_import_certificate (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  TsJobTaskRel Job Task jobTaskR (ts_import_job_task Job Task jobTaskR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition ts_target_decide_eq (Task : eqType) (x y : Task) :
    ImportedTaskSchedule.Bool :=
  ImportedTaskSchedule.Decidable_decide (Lean.eq x y)
    (ar_decidable_eq Task x y).

Lemma ts_decide_eq_related (Task : eqType) (x y : Task) :
  ArBoolRel (x == y) (ts_target_decide_eq Task x y).
Proof.
  apply ar_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP => Heq. exact (coq_eq_to_imported_eq _ _ Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq _ _ Heq).
Qed.

Lemma ts_nil_eq_isEmpty_related {T : eqType}
    (xsR : seq T) (xsL : ImportedTaskSchedule.List T) :
  ArListRel xsR xsL ->
  ArBoolRel (xsR == [::]) (ImportedTaskSchedule.List_isEmpty T xsL).
Proof.
  intro Hxs. unfold ArBoolRel, ArListRel in *.
  destruct xsR as [|x xs]; cbn [eqseq ar_bool_to_imported
    ar_list_to_imported].
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (ImportedTaskSchedule.Prosa_Validation_TaskScheduleInterface_production_isEmpty_nil T))
      (sub_imported_eq_congr (ImportedTaskSchedule.List_isEmpty T)
        _ _ Hxs)).
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (ImportedTaskSchedule.Prosa_Validation_TaskScheduleInterface_production_isEmpty_cons
          T x (ar_list_to_imported xs)))
      (sub_imported_eq_congr (ImportedTaskSchedule.List_isEmpty T)
        _ _ Hxs)).
Qed.

Definition ts_target_job_fold {T : Type} (f : T -> Lean.Nat)
    (xs : ImportedTaskSchedule.List T) : Lean.Nat :=
  ImportedTaskSchedule.List_foldr_inst2 T Lean.Nat
    (fun x total => svc_target_add (f x) total) svc_target_zero xs.

Fixpoint ts_job_fold_canonical {T : Type}
    (fR : T -> nat) (fL : T -> Lean.Nat)
    (Hf : forall x, SubNatRel (fR x) (fL x)) (xs : seq T) :
  SubNatRel (foldr (fun x total => fR x + total) O xs)
    (ts_target_job_fold fL (ar_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (sub_nat_rel_canonical O).
  - exact (svc_target_add_related (fR x) (fL x)
      (foldr (fun y total => fR y + total) O xs)
      (ts_target_job_fold fL (ar_list_to_imported xs))
      (Hf x) (@ts_job_fold_canonical T fR fL Hf xs)).
Defined.

Lemma ts_job_fold_related {T : Type}
    (fR : T -> nat) (fL : T -> Lean.Nat)
    (xsR : seq T) (xsL : ImportedTaskSchedule.List T) :
  (forall x, SubNatRel (fR x) (fL x)) -> ArListRel xsR xsL ->
  SubNatRel (foldr (fun x total => fR x + total) O xsR)
    (ts_target_job_fold fL xsL).
Proof.
  intros Hf Hxs. unfold ArListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _
    (@ts_job_fold_canonical T fR fL Hf xsR)
    (sub_imported_eq_congr (ts_target_job_fold fL) _ _ Hxs)).
Qed.

Lemma ts_mathcomp_big_seq_as_fold {T : Type}
    (xs : seq T) (f : T -> nat) :
  Logic.eq (\sum_(x <- xs) f x)
    (foldr (fun x total => f x + total) O xs).
Proof.
  elim: xs => [|x xs IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons /= IH. reflexivity.
Qed.

Section TaskScheduleCorrespondence.
  Context (Task Job : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskSchedule.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task).
  Hypothesis HjobTask : TsJobTaskRel Job Task jobTaskR jobTaskL.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Context (PStateL : ImportedTaskSchedule.Prosa_Behavior_Schedule_ProcessorState
    Job (ar_decidable_eq Job)).
  Context (R : SvcProcessorStateRel Job PStateR PStateL).
  Context (schedR : @prosa.behavior.schedule.schedule Job PStateR).
  Context (schedL : ImportedTaskSchedule.Prosa_Behavior_Schedule_schedule
    Job (ar_decidable_eq Job) PStateL).
  Context (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL).
  Context (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job).
  Context (arrL : ImportedTaskSchedule.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job)).
  Context (Harr : ArArrivalSequenceRel Job arrR arrL).
  Context (tsk : Task).

  Lemma ts_job_of_task_related (j : Job) :
    ArBoolRel
      (@prosa.model.task.concept.job_of_task Job Task jobTaskR tsk j)
      (ImportedTaskSchedule.Prosa_Model_Task_Concept_job_of_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
        jobTaskL tsk j).
  Proof.
    cbn [ImportedTaskSchedule.Prosa_Model_Task_Concept_job_of_task].
    exact (sub_imported_eq_trans _ _ _
      (ts_decide_eq_related Task
        (@prosa.model.task.concept.job_task Job Task jobTaskR j) tsk)
      (sub_imported_eq_congr
        (fun x => ts_target_decide_eq Task x tsk) _ _ (HjobTask j))).
  Qed.

  Lemma ts_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (ImportedTaskSchedule.Prosa_Behavior_Service_scheduled_at
        Job (ar_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.scheduled_at.
    cbn [ImportedTaskSchedule.Prosa_Behavior_Service_scheduled_at].
    exact (svc_scheduled_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma ts_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (ImportedTaskSchedule.Prosa_Behavior_Service_service_at
        Job (ar_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [ImportedTaskSchedule.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma ts_receives_service_at_related (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
      (ImportedTaskSchedule.Prosa_Behavior_Service_receives_service_at
        Job (ar_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.receives_service_at.
    cbn [ImportedTaskSchedule.Prosa_Behavior_Service_receives_service_at].
    apply svc_decide_lt_related.
    - exact (sub_nat_rel_canonical O).
    - exact (ts_service_at_related j tR tL Ht).
  Qed.

  Lemma ts_arrivals_up_to_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel (prosa.behavior.arrival_sequence.arrivals_up_to arrR tR)
      (ImportedTaskSchedule.Prosa_Behavior_Arrival_sequence_arrivals_up_to
        Job (ar_decidable_eq Job) arrL tL).
  Proof.
    intro Ht. cbn.
    exact (ar_bigCatNat_related_any Job arrR arrL
      O tR.+1 Lean.Nat_zero (Lean.Nat_succ tL)
      Harr (sub_nat_rel_canonical O)
      (sub_imported_eq_congr Lean.Nat_succ _ _ Ht)).
  Qed.

  Theorem scheduled_jobs_of_task_at_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at
        Task Job jobTaskR arrR PStateR schedR tsk tR)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at.
    cbn [ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at
      ImportedTaskSchedule.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at].
    apply ar_filter_related.
    - intro j. exact (ts_job_of_task_related j).
    - apply ar_filter_related.
      + intro j. exact (ts_scheduled_at_related j tR tL Ht).
      + exact (ts_arrivals_up_to_related tR tL Ht).
  Qed.

  Theorem task_scheduled_at_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.analysis.definitions.task_schedule.task_scheduled_at
        Task Job jobTaskR arrR PStateR schedR tsk tR)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.task_schedule.task_scheduled_at.
    cbn [ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at].
    apply svc_bool_not_related.
    apply ts_nil_eq_isEmpty_related.
    exact (scheduled_jobs_of_task_at_correspondence tR tL Ht).
  Qed.

  Theorem task_service_at_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel
      (@prosa.analysis.definitions.task_schedule.task_service_at
        Task Job jobTaskR arrR PStateR schedR tsk tR)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_at
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.task_schedule.task_service_at.
    rewrite ts_mathcomp_big_seq_as_fold.
    cbn [ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_at].
    apply ts_job_fold_related.
    - intro j. exact (ts_service_at_related j tR tL Ht).
    - exact (scheduled_jobs_of_task_at_correspondence tR tL Ht).
  Qed.

  Theorem task_service_during_correspondence
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.analysis.definitions.task_schedule.task_service_during
        Task Job jobTaskR arrR PStateR schedR tsk t1R t2R)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_during
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.analysis.definitions.task_schedule.task_service_at
        Task Job jobTaskR arrR PStateR schedR tsk t)
      (fun t => ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_at
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk t)
      Ht1 Ht2 (fun tR tL Ht => task_service_at_correspondence tR tL Ht).
    change (SubNatRel
      (@prosa.analysis.definitions.task_schedule.task_service_during
        Task Job jobTaskR arrR PStateR schedR tsk t1R t2R)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service_during
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Theorem task_service_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel
      (@prosa.analysis.definitions.task_schedule.task_service
        Task Job jobTaskR arrR PStateR schedR tsk tR)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.task_schedule.task_service.
    cbn [ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_service].
    exact (task_service_during_correspondence O tR Lean.Nat_zero tL
      (sub_nat_rel_canonical O) Ht).
  Qed.

  Theorem served_jobs_of_task_at_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.analysis.definitions.task_schedule.served_jobs_of_task_at
        Task Job jobTaskR arrR PStateR schedR tsk tR)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.task_schedule.served_jobs_of_task_at.
    cbn [ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at].
    apply ar_filter_related.
    - intro j. exact (ts_receives_service_at_related j tR tL Ht).
    - exact (scheduled_jobs_of_task_at_correspondence tR tL Ht).
  Qed.

  Theorem task_served_at_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.analysis.definitions.task_schedule.task_served_at
        Task Job jobTaskR arrR PStateR schedR tsk tR)
      (ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_served_at
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jobTaskL
        PStateL arrL schedL tsk tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.task_schedule.task_served_at.
    cbn [ImportedTaskSchedule.Prosa_Analysis_Definitions_TaskSchedule_task_served_at].
    apply svc_bool_not_related.
    apply ts_nil_eq_isEmpty_related.
    exact (served_jobs_of_task_at_correspondence tR tL Ht).
  Qed.
End TaskScheduleCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN scheduled_jobs_of_task_at". exact I. Qed.
Print Assumptions scheduled_jobs_of_task_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END scheduled_jobs_of_task_at". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN task_scheduled_at". exact I. Qed.
Print Assumptions task_scheduled_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END task_scheduled_at". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN task_service_at". exact I. Qed.
Print Assumptions task_service_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END task_service_at". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN task_service_during". exact I. Qed.
Print Assumptions task_service_during_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END task_service_during". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN task_service". exact I. Qed.
Print Assumptions task_service_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END task_service". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN served_jobs_of_task_at". exact I. Qed.
Print Assumptions served_jobs_of_task_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END served_jobs_of_task_at". exact I. Qed.
Goal Logic.True.
Proof. idtac "AUDIT_BEGIN task_served_at". exact I. Qed.
Print Assumptions task_served_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END task_served_at". exact I. Qed.
