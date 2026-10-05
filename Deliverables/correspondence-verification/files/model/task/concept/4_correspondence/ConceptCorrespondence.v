From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.concept.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskConcept ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyArrivalBaseAdapter
  ConceptOperations ReadyArrivalCorrespondence ConceptClasses.

(** All v0.6 Concept value definitions and two theorem types are related to
    their exact imported Lean bodies.  Abstract class observations are related
    inputs, with canonical import/export witnesses in ConceptClasses. *)

Section TaskBounds.

  Context (Task : eqType).
  Variable costR : prosa.model.task.concept.TaskCost Task.
  Variable costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost
    Task (ar_decidable_eq Task).
  Hypothesis Hcost : CtTaskCostRel Task costR costL.

  Lemma task_cost_positive_correspondence (tsk : Task) :
    ArBoolRel
      (@prosa.model.task.concept.task_cost_positive Task costR tsk)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_task_cost_positive
        Task (ar_decidable_eq Task) costL tsk).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_task_cost_positive].
    exact (ar_decide_lt_related 0 Lean.Nat_zero
      (@prosa.model.task.concept.task_cost Task costR tsk)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_task_cost
        Task (ar_decidable_eq Task) costL tsk)
      (sub_nat_rel_canonical 0) (Hcost tsk)).
  Qed.

  Variable deadlineR : prosa.model.task.concept.TaskDeadline Task.
  Variable deadlineL :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline
      Task (ar_decidable_eq Task).
  Hypothesis Hdeadline : CtTaskDeadlineRel Task deadlineR deadlineL.

  Lemma task_cost_at_most_deadline_correspondence (tsk : Task) :
    ArBoolRel
      (@prosa.model.task.concept.task_cost_at_most_deadline Task
        costR deadlineR tsk)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_task_cost_at_most_deadline
        Task (ar_decidable_eq Task) costL deadlineL tsk).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_task_cost_at_most_deadline].
    exact (ar_decide_le_related _ _ _ _ (Hcost tsk) (Hdeadline tsk)).
  Qed.

End TaskBounds.

Section JobCostBounds.

  Context (Job Task : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task).
  Hypothesis HjobTask : CtJobTaskRel Job Task jobTaskR jobTaskL.

  Variable taskCostR : prosa.model.task.concept.TaskCost Task.
  Variable taskCostL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost
    Task (ar_decidable_eq Task).
  Hypothesis HtaskCost : CtTaskCostRel Task taskCostR taskCostL.

  Variable jobCostR : prosa.behavior.job.JobCost Job.
  Variable jobCostL : ImportedTaskConcept.Prosa_Behavior_Job_JobCost
    Job (ar_decidable_eq Job).
  Hypothesis HjobCost : CtJobCostRel Job jobCostR jobCostL.

  Lemma ct_job_task_cost_related (j : Job) :
    SubNatRel
      (@prosa.model.task.concept.task_cost Task taskCostR
        (@prosa.model.task.concept.job_task Job Task jobTaskR j))
      (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_task_cost
        Task (ar_decidable_eq Task) taskCostL
        (ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_job_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
          jobTaskL j)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (HtaskCost (@prosa.model.task.concept.job_task Job Task jobTaskR j))
      (sub_imported_eq_congr
        (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_task_cost
          Task (ar_decidable_eq Task) taskCostL) _ _ (HjobTask j))).
  Qed.

  Lemma valid_job_cost_correspondence (j : Job) :
    ArBoolRel
      (@prosa.model.task.concept.valid_job_cost
        Task taskCostR Job jobTaskR jobCostR j)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_valid_job_cost
        Task (ar_decidable_eq Task) taskCostL
        Job (ar_decidable_eq Job) jobTaskL jobCostL j).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_valid_job_cost].
    exact (ar_decide_le_related _ _ _ _
      (HjobCost j) (ct_job_task_cost_related j)).
  Qed.

  Lemma jobs_have_valid_job_costs_correspondence :
    PropSPropRel
      (@prosa.model.task.concept.jobs_have_valid_job_costs
        Task taskCostR Job jobTaskR jobCostR)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_jobs_have_valid_job_costs
        Task (ar_decidable_eq Task) taskCostL
        Job (ar_decidable_eq Job) jobTaskL jobCostL).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_jobs_have_valid_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_bool_truth_correspondence.
    exact (valid_job_cost_correspondence j).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL :
    ImportedTaskConcept.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma arrivals_have_valid_job_costs_correspondence :
    PropSPropRel
      (@prosa.model.task.concept.arrivals_have_valid_job_costs
        Task taskCostR Job jobTaskR jobCostR arrR)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs
        Task (ar_decidable_eq Task) taskCostL
        Job (ar_decidable_eq Job) jobTaskL jobCostL arrL).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_bool_truth_correspondence.
      exact (valid_job_cost_correspondence j).
  Qed.

End JobCostBounds.

Section MinJobCostBounds.

  Context (Job Task : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task).
  Hypothesis HjobTask : CtJobTaskRel Job Task jobTaskR jobTaskL.

  Variable taskMinCostR : prosa.model.task.concept.TaskMinCost Task.
  Variable taskMinCostL :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost
      Task (ar_decidable_eq Task).
  Hypothesis HtaskMinCost : CtTaskMinCostRel Task taskMinCostR taskMinCostL.

  Variable jobCostR : prosa.behavior.job.JobCost Job.
  Variable jobCostL : ImportedTaskConcept.Prosa_Behavior_Job_JobCost
    Job (ar_decidable_eq Job).
  Hypothesis HjobCost : CtJobCostRel Job jobCostR jobCostL.

  Lemma ct_job_task_min_cost_related (j : Job) :
    SubNatRel
      (@prosa.model.task.concept.task_min_cost Task taskMinCostR
        (@prosa.model.task.concept.job_task Job Task jobTaskR j))
      (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost
        Task (ar_decidable_eq Task) taskMinCostL
        (ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_job_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
          jobTaskL j)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (HtaskMinCost (@prosa.model.task.concept.job_task Job Task jobTaskR j))
      (sub_imported_eq_congr
        (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost
          Task (ar_decidable_eq Task) taskMinCostL) _ _ (HjobTask j))).
  Qed.

  Lemma valid_min_job_cost_correspondence (j : Job) :
    ArBoolRel
      (@prosa.model.task.concept.valid_min_job_cost
        Task taskMinCostR Job jobTaskR jobCostR j)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_valid_min_job_cost
        Task (ar_decidable_eq Task) taskMinCostL
        Job (ar_decidable_eq Job) jobTaskL jobCostL j).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_valid_min_job_cost].
    exact (ar_decide_le_related _ _ _ _
      (ct_job_task_min_cost_related j) (HjobCost j)).
  Qed.

  Lemma jobs_have_valid_min_job_costs_correspondence :
    PropSPropRel
      (@prosa.model.task.concept.jobs_have_valid_min_job_costs
        Task taskMinCostR Job jobTaskR jobCostR)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_jobs_have_valid_min_job_costs
        Task (ar_decidable_eq Task) taskMinCostL
        Job (ar_decidable_eq Job) jobTaskL jobCostL).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_jobs_have_valid_min_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_bool_truth_correspondence.
    exact (valid_min_job_cost_correspondence j).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL :
    ImportedTaskConcept.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma arrivals_have_valid_min_job_costs_correspondence :
    PropSPropRel
      (@prosa.model.task.concept.arrivals_have_valid_min_job_costs
        Task taskMinCostR Job jobTaskR jobCostR arrR)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_arrivals_have_valid_min_job_costs
        Task (ar_decidable_eq Task) taskMinCostL
        Job (ar_decidable_eq Job) jobTaskL jobCostL arrL).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_arrivals_have_valid_min_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_bool_truth_correspondence.
      exact (valid_min_job_cost_correspondence j).
  Qed.

End MinJobCostBounds.

Section TaskSets.

  Context (Job Task : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task).
  Hypothesis HjobTask : CtJobTaskRel Job Task jobTaskR jobTaskL.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL :
    ImportedTaskConcept.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Variable tsR : prosa.model.task.concept.TaskSet Task.
  Variable tsL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskSet Task.
  Hypothesis Hts : CtTaskSetRel Task tsR tsL.

  Lemma all_jobs_from_taskset_correspondence :
    PropSPropRel
      (@prosa.model.task.concept.all_jobs_from_taskset
        Task Job jobTaskR arrR tsR)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_all_jobs_from_taskset
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job)
        jobTaskL arrL tsL).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_bool_truth_correspondence.
      exact (sub_imported_eq_trans _ _ _
        (ar_decide_mem_related Task
          (@prosa.model.task.concept.job_task Job Task jobTaskR j)
          tsR tsL Hts)
        (sub_imported_eq_congr
          (fun tsk => ar_target_decide_mem Task tsk tsL) _ _
          (HjobTask j))).
  Qed.

End TaskSets.

Section TaskIdentity.

  Context (Job Task : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task).
  Hypothesis HjobTask : CtJobTaskRel Job Task jobTaskR jobTaskL.

  Lemma same_task_correspondence (j1 j2 : Job) :
    ArBoolRel
      (@prosa.model.task.concept.same_task Job Task jobTaskR j1 j2)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_same_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
        jobTaskL j1 j2).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_same_task].
    exact (sub_imported_eq_trans _ _ _
      (ct_decide_eq_related Task
        (@prosa.model.task.concept.job_task Job Task jobTaskR j1)
        (@prosa.model.task.concept.job_task Job Task jobTaskR j2))
      (sub_imported_eq_congr2 (ct_target_decide_eq Task) _ _ _ _
        (HjobTask j1) (HjobTask j2))).
  Qed.

  Lemma same_task_sym_correspondence (j1 j2 : Job) :
    PropSPropRel
      (Logic.eq
        (@prosa.model.task.concept.same_task Job Task jobTaskR j1 j2)
        (@prosa.model.task.concept.same_task Job Task jobTaskR j2 j1))
      (Lean.eq
        (ImportedTaskConcept.Prosa_Model_Task_Concept_same_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
          jobTaskL j1 j2)
        (ImportedTaskConcept.Prosa_Model_Task_Concept_same_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
          jobTaskL j2 j1)).
  Proof.
    apply ar_bool_eq_correspondence.
    - exact (same_task_correspondence j1 j2).
    - exact (same_task_correspondence j2 j1).
  Qed.

  Lemma job_of_task_correspondence (tsk : Task) (j : Job) :
    ArBoolRel
      (@prosa.model.task.concept.job_of_task Job Task jobTaskR tsk j)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_job_of_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
        jobTaskL tsk j).
  Proof.
    cbn [ImportedTaskConcept.Prosa_Model_Task_Concept_job_of_task].
    exact (sub_imported_eq_trans _ _ _
      (ct_decide_eq_related Task
        (@prosa.model.task.concept.job_task Job Task jobTaskR j) tsk)
      (sub_imported_eq_congr
        (fun t => ct_target_decide_eq Task t tsk) _ _ (HjobTask j))).
  Qed.

  Lemma diff_task_correspondence (tsk : Task) (j1 j2 : Job) :
    PropSPropRel
      (is_true
        (@prosa.model.task.concept.job_of_task Job Task jobTaskR tsk j1)
        -> is_true (~~
          (@prosa.model.task.concept.job_of_task Job Task jobTaskR tsk j2))
        -> is_true (~~
          (@prosa.model.task.concept.same_task Job Task jobTaskR j1 j2)))
      (Lean.eq
        (ImportedTaskConcept.Prosa_Model_Task_Concept_job_of_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
          jobTaskL tsk j1) ImportedTaskConcept.Bool_true
        -> Lean.eq
          (ImportedTaskConcept.Prosa_Model_Task_Concept_job_of_task
            Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
            jobTaskL tsk j2) ImportedTaskConcept.Bool_false
        -> Lean.eq
          (ImportedTaskConcept.Prosa_Model_Task_Concept_same_task
            Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
            jobTaskL j1 j2) ImportedTaskConcept.Bool_false).
  Proof.
    apply ar_imp_correspondence.
    - apply ar_bool_truth_correspondence.
      exact (job_of_task_correspondence tsk j1).
    - apply ar_imp_correspondence.
      + apply ct_bool_false_correspondence.
        exact (job_of_task_correspondence tsk j2).
      + apply ct_bool_false_correspondence.
        exact (same_task_correspondence j1 j2).
  Qed.

End TaskIdentity.

Print Assumptions task_cost_positive_correspondence.
Print Assumptions task_cost_at_most_deadline_correspondence.
Print Assumptions valid_job_cost_correspondence.
Print Assumptions jobs_have_valid_job_costs_correspondence.
Print Assumptions arrivals_have_valid_job_costs_correspondence.
Print Assumptions valid_min_job_cost_correspondence.
Print Assumptions jobs_have_valid_min_job_costs_correspondence.
Print Assumptions arrivals_have_valid_min_job_costs_correspondence.
Print Assumptions all_jobs_from_taskset_correspondence.
Print Assumptions same_task_correspondence.
Print Assumptions same_task_sym_correspondence.
Print Assumptions job_of_task_correspondence.
Print Assumptions diff_task_correspondence.
