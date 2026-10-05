# `same_task_sym`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.concept.same_task_sym`
- Lean: `Prosa.Model.Task.Concept.same_task_sym`
- Certificate: ``

## Official Rocq

```coq
same_task_sym :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (j1 j2 : Equality.sort Job),
@same_task Job Task H j1 j2 = @same_task Job Task H j2 j1

same_task_sym is not universe polymorphic
Arguments same_task_sym {Job Task H} j1 j2
same_task_sym is opaque
Expands to: Constant prosa.model.task.concept.same_task_sym
Declared in library prosa.model.task.concept, line 172, characters 9-22
@same_task_sym
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (j1 j2 : Equality.sort Job),
       @same_task Job Task H j1 j2 = @same_task Job Task H j2 j1
```

## Lean

```lean
@Prosa.Model.Task.Concept.same_task_sym : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (j1 j2 : Job),
  Prosa.Model.Task.Concept.same_task j1 j2 = Prosa.Model.Task.Concept.same_task j2 j1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_same_task_sym
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                            Job
                                                                            inst_3
                                                                            Task
                                                                            inst_7)
         (j1 j2 : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_same_task Job inst_3
            Task inst_7
            inst_10 j1 j2)
         (Prosa_Model_Task_Concept_same_task Job inst_3
            Task inst_7
            inst_10 j2 j1)
```
