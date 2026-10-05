From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.arrival.sporadic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSporadic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence.
From SporadicCertificates Require Import SporadicBaseAdapter
  SporadicOperations SporadicClasses.

(** All displayed target constants are from the actual compiled Sporadic.olean
    import.  The hypotheses on inputs below are ordinary representation
    relations, with canonical constructors in SporadicClasses. *)

Lemma sp_eq_correspondence (T : Type) (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hy)))).
Qed.

Lemma sp_false_correspondence :
  PropSPropRel Logic.False ImportedSporadic.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma sp_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (ImportedSporadic.Ne T x y).
Proof.
  unfold ImportedSporadic.Ne, ImportedSporadic.Not.
  apply ar_imp_correspondence.
  - exact (sp_eq_correspondence T x x y y
      (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact sp_false_correspondence.
Qed.

Lemma sp_valid_task_min_inter_arrival_time_certificate (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task)) :
  SpSporadicModelRel Task modelR modelL ->
  forall tsk : Task,
  ArBoolRel
    (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time
      Task modelR tsk)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
      Task (ar_decidable_eq Task) modelL tsk).
Proof.
  intros Hmodel tsk. cbn.
  apply ar_decide_lt_related.
  - exact (sub_nat_rel_canonical 0).
  - exact (Hmodel tsk).
Qed.

Lemma sp_valid_taskset_inter_arrival_times_certificate (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task))
    (tsR : prosa.model.task.concept.TaskSet Task)
    (tsL : ImportedSporadic.Prosa_Model_Task_Concept_TaskSet Task) :
  SpSporadicModelRel Task modelR modelL ->
  SpTaskSetRel Task tsR tsL ->
  PropSPropRel
    (@prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times
      Task modelR tsR)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times
      Task (ar_decidable_eq Task) modelL tsL).
Proof.
  intros Hmodel Hts. cbn.
  apply ar_forall_identity_correspondence. intro tsk.
  apply ar_imp_correspondence.
  - apply ar_bool_truth_correspondence.
    exact (ar_decide_mem_related Task tsk tsR tsL Hts).
  - apply ar_bool_truth_correspondence.
    exact (sp_valid_task_min_inter_arrival_time_certificate
      Task modelR modelL Hmodel tsk).
Qed.

Print Assumptions sp_valid_task_min_inter_arrival_time_certificate.
Print Assumptions sp_valid_taskset_inter_arrival_times_certificate.

Definition sp_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSporadic.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSporadic.instHAdd_inst1 Lean.Nat
      ImportedSporadic.instAddNat) a b.

Lemma sp_target_add_is_certified (a b : Lean.Nat) :
  Lean.eq (sp_target_add a b) (sub_imported_add a b).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma sp_respects_sporadic_task_model_certificate (Task Job : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task))
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedSporadic.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task))
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : ImportedSporadic.Prosa_Behavior_Job_JobArrival
      Job (ar_decidable_eq Job))
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (arrL : ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job)) (tsk : Task) :
  SpSporadicModelRel Task modelR modelL ->
  SpJobTaskRel Job Task jobTaskR jobTaskL ->
  SpJobArrivalRel Job arrivalR arrivalL ->
  ArArrivalSequenceRel Job arrR arrL ->
  PropSPropRel
    (@prosa.model.task.arrival.sporadic.respects_sporadic_task_model
      Task modelR Job jobTaskR arrivalR arrR tsk)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model
      Task (ar_decidable_eq Task) modelL Job (ar_decidable_eq Job)
      jobTaskL arrivalL arrL tsk).
Proof.
  intros Hmodel HjobTask Harrival Harr.
  cbn [prosa.model.task.arrival.sporadic.respects_sporadic_task_model
    ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model].
  apply ar_forall_identity_correspondence. intro j.
  apply ar_forall_identity_correspondence. intro j'.
  apply ar_imp_correspondence.
  - exact (sp_neq_correspondence Job j j').
  - apply ar_imp_correspondence.
    + exact (sp_arrives_in_correspondence Job arrR arrL j Harr).
    + apply ar_imp_correspondence.
      * exact (sp_arrives_in_correspondence Job arrR arrL j' Harr).
      * apply ar_imp_correspondence.
        -- apply sp_eq_correspondence.
           ++ exact (HjobTask j).
           ++ exact (@Lean.eq_refl _ _).
        -- apply ar_imp_correspondence.
           ++ apply sp_eq_correspondence.
              ** exact (HjobTask j').
              ** exact (@Lean.eq_refl _ _).
           ++ apply ar_imp_correspondence.
              ** exact (sub_nat_le_correspondence _ _ _ _
                   (Harrival j) (Harrival j')).
              ** apply sub_nat_le_correspondence.
                 --- exact (sub_imported_eq_trans _ _ _
                       (sub_add_correspondence _ _ _ _
                         (Harrival j) (Hmodel tsk))
                       (sub_imported_eq_sym _ _
                         (sp_target_add_is_certified _ _))).
                 --- exact (Harrival j').
Qed.

Lemma sp_taskset_respects_sporadic_task_model_certificate (Task Job : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task))
    (tsR : prosa.model.task.concept.TaskSet Task)
    (tsL : ImportedSporadic.Prosa_Model_Task_Concept_TaskSet Task)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedSporadic.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task))
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : ImportedSporadic.Prosa_Behavior_Job_JobArrival
      Job (ar_decidable_eq Job))
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (arrL : ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job)) :
  SpSporadicModelRel Task modelR modelL ->
  SpTaskSetRel Task tsR tsL ->
  SpJobTaskRel Job Task jobTaskR jobTaskL ->
  SpJobArrivalRel Job arrivalR arrivalL ->
  ArArrivalSequenceRel Job arrR arrL ->
  PropSPropRel
    (@prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model
      Task modelR tsR Job jobTaskR arrivalR arrR)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model
      Task (ar_decidable_eq Task) modelL tsL Job (ar_decidable_eq Job)
      jobTaskL arrivalL arrL).
Proof.
  intros Hmodel Hts HjobTask Harrival Harr.
  cbn [prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model
    ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model].
  apply ar_forall_identity_correspondence. intro tsk.
  apply ar_imp_correspondence.
  - apply ar_bool_truth_correspondence.
    exact (ar_decide_mem_related Task tsk tsR tsL Hts).
  - exact (sp_respects_sporadic_task_model_certificate
      Task Job modelR modelL jobTaskR jobTaskL arrivalR arrivalL
      arrR arrL tsk Hmodel HjobTask Harrival Harr).
Qed.

Print Assumptions sp_target_add_is_certified.
Print Assumptions sp_respects_sporadic_task_model_certificate.
Print Assumptions sp_taskset_respects_sporadic_task_model_certificate.

Lemma sp_valid_task_min_inter_arrival_time_canonical (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (tsk : Task) :
  ArBoolRel
    (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time
      Task modelR tsk)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
      Task (ar_decidable_eq Task)
      (sp_import_sporadic_model Task modelR) tsk).
Proof.
  exact (sp_valid_task_min_inter_arrival_time_certificate Task modelR
    (sp_import_sporadic_model Task modelR)
    (sp_sporadic_model_import_certificate Task modelR) tsk).
Qed.

Lemma sp_valid_taskset_inter_arrival_times_canonical (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (tsR : prosa.model.task.concept.TaskSet Task) :
  PropSPropRel
    (@prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times
      Task modelR tsR)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times
      Task (ar_decidable_eq Task)
      (sp_import_sporadic_model Task modelR)
      (sp_import_task_set Task tsR)).
Proof.
  exact (sp_valid_taskset_inter_arrival_times_certificate Task modelR
    (sp_import_sporadic_model Task modelR) tsR
    (sp_import_task_set Task tsR)
    (sp_sporadic_model_import_certificate Task modelR)
    (sp_task_set_import_certificate Task tsR)).
Qed.

Lemma sp_respects_sporadic_task_model_canonical (Task Job : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (tsk : Task) :
  PropSPropRel
    (@prosa.model.task.arrival.sporadic.respects_sporadic_task_model
      Task modelR Job jobTaskR arrivalR arrR tsk)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model
      Task (ar_decidable_eq Task)
      (sp_import_sporadic_model Task modelR)
      Job (ar_decidable_eq Job)
      (sp_import_job_task Job Task jobTaskR)
      (sp_import_job_arrival Job arrivalR)
      (ar_arrival_sequence_to_imported Job arrR) tsk).
Proof.
  exact (sp_respects_sporadic_task_model_certificate
    Task Job modelR (sp_import_sporadic_model Task modelR)
    jobTaskR (sp_import_job_task Job Task jobTaskR)
    arrivalR (sp_import_job_arrival Job arrivalR)
    arrR (ar_arrival_sequence_to_imported Job arrR) tsk
    (sp_sporadic_model_import_certificate Task modelR)
    (sp_job_task_import_certificate Job Task jobTaskR)
    (sp_job_arrival_import_certificate Job arrivalR)
    (ar_arrival_sequence_canonical Job arrR)).
Qed.

Lemma sp_taskset_respects_sporadic_task_model_canonical (Task Job : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (tsR : prosa.model.task.concept.TaskSet Task)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job) :
  PropSPropRel
    (@prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model
      Task modelR tsR Job jobTaskR arrivalR arrR)
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model
      Task (ar_decidable_eq Task)
      (sp_import_sporadic_model Task modelR)
      (sp_import_task_set Task tsR)
      Job (ar_decidable_eq Job)
      (sp_import_job_task Job Task jobTaskR)
      (sp_import_job_arrival Job arrivalR)
      (ar_arrival_sequence_to_imported Job arrR)).
Proof.
  exact (sp_taskset_respects_sporadic_task_model_certificate
    Task Job modelR (sp_import_sporadic_model Task modelR)
    tsR (sp_import_task_set Task tsR)
    jobTaskR (sp_import_job_task Job Task jobTaskR)
    arrivalR (sp_import_job_arrival Job arrivalR)
    arrR (ar_arrival_sequence_to_imported Job arrR)
    (sp_sporadic_model_import_certificate Task modelR)
    (sp_task_set_import_certificate Task tsR)
    (sp_job_task_import_certificate Job Task jobTaskR)
    (sp_job_arrival_import_certificate Job arrivalR)
    (ar_arrival_sequence_canonical Job arrR)).
Qed.

Print Assumptions sp_valid_task_min_inter_arrival_time_canonical.
Print Assumptions sp_valid_taskset_inter_arrival_times_canonical.
Print Assumptions sp_respects_sporadic_task_model_canonical.
Print Assumptions sp_taskset_respects_sporadic_task_model_canonical.
