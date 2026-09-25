From prosa Require Import model.task.concept.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskConcept.

(** Source types are elaborated from the pinned, byte-identical v0.6 file.
    Target types are read from the compiled and imported Lean artifact. *)
Check prosa.model.task.concept.TaskType.
Check @prosa.model.task.concept.JobTask.
Check @prosa.model.task.concept.TaskDeadline.
Check @prosa.model.task.concept.TaskCost.
Check @prosa.model.task.concept.TaskMinCost.
Check @prosa.model.task.concept.task_cost_positive.
Check @prosa.model.task.concept.task_cost_at_most_deadline.
Check @prosa.model.task.concept.valid_job_cost.
Check @prosa.model.task.concept.jobs_have_valid_job_costs.
Check @prosa.model.task.concept.arrivals_have_valid_job_costs.
Check @prosa.model.task.concept.valid_min_job_cost.
Check @prosa.model.task.concept.jobs_have_valid_min_job_costs.
Check @prosa.model.task.concept.arrivals_have_valid_min_job_costs.
Check @prosa.model.task.concept.TaskSet.
Check @prosa.model.task.concept.all_jobs_from_taskset.
Check @prosa.model.task.concept.same_task.
Check @prosa.model.task.concept.same_task_sym.
Check @prosa.model.task.concept.job_of_task.
Check @prosa.model.task.concept.diff_task.

Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskType.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_mk.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_job_task.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline_mk.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline_task_deadline.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_mk.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_task_cost.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_mk.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_task_cost_positive.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_task_cost_at_most_deadline.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_valid_job_cost.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_jobs_have_valid_job_costs.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_valid_min_job_cost.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_jobs_have_valid_min_job_costs.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_arrivals_have_valid_min_job_costs.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_TaskSet.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_all_jobs_from_taskset.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_same_task.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_same_task_sym.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_job_of_task.
Check ImportedTaskConcept.Prosa_Model_Task_Concept_diff_task.
