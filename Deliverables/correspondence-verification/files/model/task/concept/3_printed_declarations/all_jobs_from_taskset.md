# `all_jobs_from_taskset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.all_jobs_from_taskset`
- Lean: `Prosa.Model.Task.Concept.all_jobs_from_taskset`
- Certificate: ``

## Official Rocq

```coq
all_jobs_from_taskset :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop

all_jobs_from_taskset is not universe polymorphic
Arguments all_jobs_from_taskset {Task Job H0} arr_seq ts
all_jobs_from_taskset is transparent
Expands to: Constant prosa.model.task.concept.all_jobs_from_taskset
Declared in library prosa.model.task.concept, line 151, characters 13-34
@all_jobs_from_taskset
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
all_jobs_from_taskset =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (ts : TaskSet (Equality.sort Task)) =>
forall j : Equality.sort Job, @arrives_in Job arr_seq j -> is_true (@job_task Job Task H0 j \in ts)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop

Arguments all_jobs_from_taskset {Task Job H0} arr_seq ts
```

## Lean

```lean
@Prosa.Model.Task.Concept.all_jobs_from_taskset : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Model.Task.Concept.TaskSet Task → Prop
def Prosa.Model.Task.Concept.all_jobs_from_taskset.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] arrSeq ts =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j → decide (Prosa.Model.Task.Concept.job_task j ∈ ts) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_all_jobs_from_taskset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Concept_all_jobs_from_taskset@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                     inst_10
                                                                     Task
                                                                     inst_3)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_10)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job inst_10
  arrSeq j ->
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_10 Task
           inst_3
           inst_13 j))
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_10 Task
           inst_3
           inst_13 j)
        ts))
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Concept_all_jobs_from_taskset Task
  inst_3 Job
  inst_10
  inst_13 arrSeq ts
```
