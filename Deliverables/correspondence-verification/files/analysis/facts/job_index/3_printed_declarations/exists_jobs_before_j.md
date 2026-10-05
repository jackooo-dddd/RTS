# `exists_jobs_before_j`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.exists_jobs_before_j`
- Lean: `Prosa.Analysis.Facts.JobIndex.exists_jobs_before_j`
- Certificate: `exists_jobs_before_j_correspondence`

## Official Rocq

```coq
exists_jobs_before_j :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall k : nat,
is_true (k < @job_index Task Job H0 H arr_seq j) ->
exists j' : Equality.sort Job,
  j <> j' /\
  @job_task Job Task H j' = @job_task Job Task H j /\
  @arrives_in Job arr_seq j' /\ @job_index Task Job H0 H arr_seq j' = k

exists_jobs_before_j is not universe polymorphic
Arguments exists_jobs_before_j {Task Job H H0} arr_seq H_valid_arrival_sequence j 
  H_arrives_in_arr_seq k%nat_scope _
exists_jobs_before_j is opaque
Expands to: Constant prosa.analysis.facts.job_index.exists_jobs_before_j
Declared in library prosa.analysis.facts.job_index, line 347, characters 8-28
@exists_jobs_before_j
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall k : nat,
       is_true (k < @job_index Task Job H0 H arr_seq j) ->
       exists j' : Equality.sort Job,
         j <> j' /\
         @job_task Job Task H j' = @job_task Job Task H j /\
         @arrives_in Job arr_seq j' /\ @job_index Task Job H0 H arr_seq j' = k
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.exists_jobs_before_j : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        ∀ k < Prosa.Model.Task.Arrivals.job_index arr_seq j,
          ∃ j',
            j ≠ j' ∧
              Prosa.Model.Task.Concept.job_task j' = Prosa.Model.Task.Concept.job_task j ∧
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' ∧
                  Prosa.Model.Task.Arrivals.job_index arr_seq j' = k
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_exists_jobs_before_j
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (inst_14 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       forall k : Nat,
       LT_lt_inst1 Nat instLTNat k
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j) ->
       Exists Job
         (fun j' : Job =>
          And (Ne Job j j')
            (And
               (@eq Task
                  (Prosa_Model_Task_Concept_JobTask_job_task Job
                     inst_7 Task
                     inst_3
                     inst_10 j')
                  (Prosa_Model_Task_Concept_JobTask_job_task Job
                     inst_7 Task
                     inst_3
                     inst_10 j))
               (And
                  (Prosa_Behavior_Arrival_sequence_arrives_in Job
                     inst_7 arr_seq j')
                  (@eq Nat
                     (Prosa_Model_Task_Arrivals_job_index Task
                        inst_3 Job
                        inst_7
                        inst_14
                        inst_10 arr_seq j')
                     k))))
```
