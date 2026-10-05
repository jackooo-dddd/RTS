# `GEL_is_reflexive`

- Kind (Rocq): Fact
- Rocq: `prosa.model.priority.gel.GEL_is_reflexive`
- Lean: `Prosa.Model.Priority.Gel.GEL_is_reflexive`
- Certificate: `GEL_is_reflexive_correspondence`

## Official Rocq

```coq
GEL_is_reflexive :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobArrival Job}
  {H1 : JobTask Job Task},
@reflexive_job_priorities Job (@GEL Job Task H H0 H1)

GEL_is_reflexive is not universe polymorphic
Arguments GEL_is_reflexive {Task H Job H0 H1} x
GEL_is_reflexive is opaque
Expands to: Constant prosa.model.priority.gel.GEL_is_reflexive
Declared in library prosa.model.priority.gel, line 60, characters 7-23
@GEL_is_reflexive
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobArrival Job)
         (H1 : JobTask Job Task),
       @reflexive_job_priorities Job (@GEL Job Task H H0 H1)
```

## Lean

```lean
@Prosa.Model.Priority.Gel.GEL_is_reflexive : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Priority.Gel.PriorityPoint Task] {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task],
  Prosa.Model.Priority.Definitions.reflexive_job_priorities (Prosa.Model.Priority.Gel.GEL Job Task)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Gel_GEL_is_reflexive
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                            Task
                                                                            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_10)
         (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                             Job
                                                                             inst_10
                                                                             Task
                                                                             inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_10
         (Prosa_Model_Priority_Gel_GEL Job inst_10
            Task inst_3
            inst_6
            inst_13
            inst_16)
```
