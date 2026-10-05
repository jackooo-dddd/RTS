# `jobs_have_valid_job_costs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.jobs_have_valid_job_costs`
- Lean: `Prosa.Model.Task.Concept.jobs_have_valid_job_costs`
- Certificate: ``

## Official Rocq

```coq
jobs_have_valid_job_costs :
forall {Task : TaskType}, TaskCost Task -> forall {Job : JobType}, JobTask Job Task -> JobCost Job -> Prop

jobs_have_valid_job_costs is not universe polymorphic
Arguments jobs_have_valid_job_costs {Task H Job H2 H3}
jobs_have_valid_job_costs is transparent
Expands to: Constant prosa.model.task.concept.jobs_have_valid_job_costs
Declared in library prosa.model.task.concept, line 76, characters 15-40
@jobs_have_valid_job_costs
     : forall Task : TaskType, TaskCost Task -> forall Job : JobType, JobTask Job Task -> JobCost Job -> Prop
```

Body:

```coq
jobs_have_valid_job_costs =
fun (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H2 : JobTask Job Task) (H3 : JobCost Job) =>
forall j : Equality.sort Job, is_true (@valid_job_cost Task H Job H2 H3 j)
     : forall {Task : TaskType},
       TaskCost Task -> forall {Job : JobType}, JobTask Job Task -> JobCost Job -> Prop

Arguments jobs_have_valid_job_costs {Task H Job H2 H3}
```

## Lean

```lean
@Prosa.Model.Task.Concept.jobs_have_valid_job_costs : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobCost Job] → Prop
def Prosa.Model.Task.Concept.jobs_have_valid_job_costs.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobCost Job] → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobCost Job] =>
  ∀ (j : Job), Prosa.Model.Task.Concept.valid_job_cost j = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_jobs_have_valid_job_costs
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_16
         Task inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_16 -> SProp
```

Body:

```coq
Prosa_Model_Task_Concept_jobs_have_valid_job_costs@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost Task
                                                                     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_16 : DecidableEq Job)
  (inst_19 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_16
                                                                      Task
                                                                      inst_3)
  (inst_23 : Prosa_Behavior_Job_JobCost Job
                                                                      inst_16) =>
forall j : Job,
@eq Bool
  (Prosa_Model_Task_Concept_valid_job_cost Task inst_3
     inst_6 Job
     inst_16
     inst_19
     inst_23 j)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_16
         Task inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_16 -> SProp

Arguments Prosa_Model_Task_Concept_jobs_have_valid_job_costs Task
  inst_3
  inst_6 Job
  inst_16
  inst_19
  inst_23
```
