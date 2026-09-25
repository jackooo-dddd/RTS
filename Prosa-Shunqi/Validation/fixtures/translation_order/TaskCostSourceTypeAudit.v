From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.analysis.facts.model.task_cost.

Definition tc_source_positive_type_guard
    (Task : prosa.model.task.concept.TaskType)
    (Job : prosa.behavior.job.JobType)
    (JT : prosa.model.task.concept.JobTask Job Task)
    (JC : prosa.behavior.job.JobCost Job)
    (TC : prosa.model.task.concept.TaskCost Task)
    (tsk : Task) (j : Job)
    (Hjob : @prosa.model.task.concept.job_of_task Job Task JT tsk j)
    (Hpositive : @prosa.model.job.properties.job_cost_positive Job JC j)
    (Hvalid : @prosa.model.task.concept.valid_job_cost Task TC Job JT JC j) :
    0 < @prosa.model.task.concept.task_cost Task TC tsk :=
  @job_cost_positive_implies_task_cost_positive
    Task Job JT JC TC tsk j Hjob Hpositive Hvalid.

Definition tc_source_sum_type_guard
    (Task : prosa.model.task.concept.TaskType)
    (TC : prosa.model.task.concept.TaskCost Task)
    (Job : prosa.behavior.job.JobType)
    (JC : prosa.behavior.job.JobCost Job)
    (JT : prosa.model.task.concept.JobTask Job Task)
    (tsk : Task) (js : seq Job)
    (Hvalid : {in js, forall j,
      @prosa.model.task.concept.job_of_task Job Task JT tsk j &&
      @prosa.model.task.concept.valid_job_cost Task TC Job JT JC j}) :
    \sum_(j <- js) @prosa.behavior.job.job_cost Job JC j <=
      @prosa.model.task.concept.task_cost Task TC tsk * size js :=
  @sum_job_costs_bounded Task TC Job JC JT tsk js Hvalid.

Set Printing Implicit.
Check @job_cost_positive_implies_task_cost_positive.
Check @sum_job_costs_bounded.
Print Assumptions job_cost_positive_implies_task_cost_positive.
Print Assumptions sum_job_costs_bounded.
