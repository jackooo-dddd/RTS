# `arrivals_between_partitioned_by_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_partitioned_by_task`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_partitioned_by_task`
- Certificate: `arrivals_between_partitioned_by_task_correspondence`

## Official Rocq

```coq
arrivals_between_partitioned_by_task :
forall {Job : JobType} {Task : TaskType} {H0 : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (ts : seq (Equality.sort Task)),
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
forall (t1 t2 : instant) (j : Equality.sort Job),
(j \in @arrivals_between Job arr_seq t1 t2) =
(j \in \cat_(tsk<-ts)@task_arrivals_between Job Task H0 arr_seq tsk t1 t2)

arrivals_between_partitioned_by_task is not universe polymorphic
Arguments arrivals_between_partitioned_by_task {Job Task H0} arr_seq ts%seq_scope 
  H_all_jobs_from_taskset t1 t2 j
arrivals_between_partitioned_by_task is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_partitioned_by_task
Declared in library prosa.analysis.facts.behavior.arrivals, line 485, characters 10-46
@arrivals_between_partitioned_by_task
     : forall (Job : JobType) (Task : TaskType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (ts : seq (Equality.sort Task)),
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       forall (t1 t2 : instant) (j : Equality.sort Job),
       (j \in @arrivals_between Job arr_seq t1 t2) =
       (j \in \cat_(tsk<-ts)@task_arrivals_between Job Task H0 arr_seq tsk t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_partitioned_by_task : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (ts : List Task),
  Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
        decide
          (j ∈
            Prosa.Util.Bigcat.bigCatSeqAll ts fun tsk =>
              Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_partitioned_by_task
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (ts : List Task),
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_7 Job
         inst_3
         inst_10 arr_seq ts ->
       forall (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t2)))
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Util_Bigcat_bigCatSeqAll Task Job ts
                  (fun tsk : Task =>
                   Prosa_Model_Task_Arrivals_task_arrivals_between Job
                     inst_3 Task
                     inst_7
                     inst_10 arr_seq tsk
                     t1 t2))
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Util_Bigcat_bigCatSeqAll Task Job ts
                  (fun tsk : Task =>
                   Prosa_Model_Task_Arrivals_task_arrivals_between Job
                     inst_3 Task
                     inst_7
                     inst_10 arr_seq tsk
                     t1 t2))))
```
