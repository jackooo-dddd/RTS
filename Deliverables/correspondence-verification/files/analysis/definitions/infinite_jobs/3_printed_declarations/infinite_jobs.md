# `infinite_jobs`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.infinite_jobs.infinite_jobs`
- Lean: `Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs`
- Certificate: `infinite_jobs_correspondence`

## Official Rocq

```coq
infinite_jobs :
forall {Task : TaskType} {Job : JobType}, JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Prop

infinite_jobs is not universe polymorphic
Arguments infinite_jobs {Task Job H H0} arr_seq
infinite_jobs is transparent
Expands to: Constant prosa.analysis.definitions.infinite_jobs.infinite_jobs
Declared in library prosa.analysis.definitions.infinite_jobs, line 21, characters 13-26
@infinite_jobs
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Prop
```

Body:

```coq
infinite_jobs =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
  (arr_seq : arrival_sequence Job) =>
forall (tsk : Equality.sort Task) (n : nat),
exists j : Equality.sort Job,
  @arrives_in Job arr_seq j /\ @job_task Job Task H j = tsk /\ @job_index Task Job H0 H arr_seq j = n
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Prop

Arguments infinite_jobs {Task Job H H0} arr_seq
```

## Lean

```lean
@Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] arr_seq =>
  ∀ (tsk : Task) (n : ℕ),
    ∃ j,
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j ∧
        Prosa.Model.Task.Concept.job_task j = tsk ∧ Prosa.Model.Task.Arrivals.job_index arr_seq j = n
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (inst_14 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7) =>
forall (tsk : Task) (n : Nat),
Exists Job
  (fun j : Job =>
   And
     (Prosa_Behavior_Arrival_sequence_arrives_in Job
        inst_7 arr_seq j)
     (And
        (@eq Task
           (Prosa_Model_Task_Concept_JobTask_job_task Job
              inst_7 Task
              inst_3
              inst_10 j)
           tsk)
        (@eq Nat
           (Prosa_Model_Task_Arrivals_job_index Task
              inst_3 Job
              inst_7
              inst_14
              inst_10 arr_seq j)
           n)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       SProp

Arguments Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 arr_seq
```
