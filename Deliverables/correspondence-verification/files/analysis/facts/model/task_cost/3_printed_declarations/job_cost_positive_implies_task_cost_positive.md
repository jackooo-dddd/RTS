# `job_cost_positive_implies_task_cost_positive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_cost.job_cost_positive_implies_task_cost_positive`
- Lean: `Prosa.Analysis.Facts.Model.TaskCost.job_cost_positive_implies_task_cost_positive`
- Certificate: `tc_positive_statement_correspondence`

## Official Rocq

```coq
job_cost_positive_implies_task_cost_positive :
forall {Task : concept.TaskType} {Job : JobType} {H : concept.JobTask Job Task} {H0 : JobCost Job}
  {H1 : concept.TaskCost Task} (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@concept.job_of_task Job Task H tsk j) ->
is_true (@job_cost_positive Job H0 j) ->
is_true (@concept.valid_job_cost Task H1 Job H H0 j) -> is_true (0 < @concept.task_cost Task H1 tsk)

job_cost_positive_implies_task_cost_positive is not universe polymorphic
Arguments job_cost_positive_implies_task_cost_positive {Task Job H H0 H1} tsk j H_job_of_task
  H_job_cost_positive H_valid_job_cost
job_cost_positive_implies_task_cost_positive is opaque
Expands to: Constant prosa.analysis.facts.model.task_cost.job_cost_positive_implies_task_cost_positive
Declared in library prosa.analysis.facts.model.task_cost, line 22, characters 8-52
@job_cost_positive_implies_task_cost_positive
     : forall (Task : concept.TaskType) (Job : JobType) (H : concept.JobTask Job Task) 
         (H0 : JobCost Job) (H1 : concept.TaskCost Task) (tsk : Equality.sort Task) 
         (j : Equality.sort Job),
       is_true (@concept.job_of_task Job Task H tsk j) ->
       is_true (@job_cost_positive Job H0 j) ->
       is_true (@concept.valid_job_cost Task H1 Job H H0 j) -> is_true (0 < @concept.task_cost Task H1 tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskCost.job_cost_positive_implies_task_cost_positive : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobCost Job] [inst_4 : Prosa.Model.Task.Concept.TaskCost Task] (tsk : Task) (j : Job),
  Prosa.Model.Task.Concept.job_of_task tsk j = true →
    Prosa.Model.Job.Properties.job_cost_positive j = true →
      Prosa.Model.Task.Concept.valid_job_cost j = true → 0 < Prosa.Model.Task.Concept.task_cost tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskCost_job_cost_positive_implies_task_cost_positive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_17 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_14 j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Concept_valid_job_cost Task
            inst_3
            inst_17 Job
            inst_7
            inst_10
            inst_14 j)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_17 tsk)
```
