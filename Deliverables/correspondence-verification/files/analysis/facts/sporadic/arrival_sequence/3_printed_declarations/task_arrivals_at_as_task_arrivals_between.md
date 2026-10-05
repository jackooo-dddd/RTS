# `task_arrivals_at_as_task_arrivals_between`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.task_arrivals_at_as_task_arrivals_between`
- Certificate: `task_arrivals_at_as_task_arrivals_between_correspondence`

## Official Rocq

```coq
task_arrivals_at_as_task_arrivals_between :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) (j1 : Equality.sort Job),
@job_task Job Task H0 j1 = tsk ->
@task_arrivals_at_job_arrival Job Task H0 H1 arr_seq j1 =
@task_arrivals_between Job Task H0 arr_seq tsk (@job_arrival Job H1 j1) (@job_arrival Job H1 j1).+1

task_arrivals_at_as_task_arrivals_between is not universe polymorphic
Arguments task_arrivals_at_as_task_arrivals_between {Task Job H0 H1} arr_seq tsk j1 H_j1_task
task_arrivals_at_as_task_arrivals_between is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between
Declared in library prosa.analysis.facts.sporadic.arrival_sequence, line 122, characters 8-49
@task_arrivals_at_as_task_arrivals_between
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) (j1 : Equality.sort Job),
       @job_task Job Task H0 j1 = tsk ->
       @task_arrivals_at_job_arrival Job Task H0 H1 arr_seq j1 =
       @task_arrivals_between Job Task H0 arr_seq tsk (@job_arrival Job H1 j1) (@job_arrival Job H1 j1).+1
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalSequence.task_arrivals_at_as_task_arrivals_between : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (j1 : Job),
  Prosa.Model.Task.Concept.job_task j1 = tsk →
    Prosa.Model.Task.Arrivals.task_arrivals_at_job_arrival arr_seq j1 =
      Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk (Prosa.Behavior.Job.job_arrival j1)
        (Prosa.Behavior.Job.job_arrival j1 + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalSequence_task_arrivals_at_as_task_arrivals_between
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10)
         (tsk : Task) (j1 : Job),
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j1)
         tsk ->
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_at_job_arrival Job
            inst_10 Task
            inst_3
            inst_13
            inst_17 arr_seq j1)
         (Prosa_Model_Task_Arrivals_task_arrivals_between Job
            inst_10 Task
            inst_3
            inst_13 arr_seq tsk
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_10
               inst_17 j1)
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_10
                  inst_17 j1)
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
```
