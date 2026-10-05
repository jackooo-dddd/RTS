# `prev_job_index_j`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.prev_job_index_j`
- Lean: `Prosa.Analysis.Facts.JobIndex.prev_job_index_j`
- Certificate: `prev_job_index_j_correspondence`

## Official Rocq

```coq
prev_job_index_j :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_index Task Job H0 H arr_seq j) ->
is_true (0 < @job_index Task Job H0 H arr_seq j) ->
@job_index Task Job H0 H arr_seq (@prev_job Job Task H H0 arr_seq j) = @job_index Task Job H0 H arr_seq j - 1

prev_job_index_j is not universe polymorphic
Arguments prev_job_index_j {Task Job H H0} arr_seq H_valid_arrival_sequence j H_arrives_in_arr_seq
  H_positive_job_index _
prev_job_index_j is opaque
Expands to: Constant prosa.analysis.facts.job_index.prev_job_index_j
Declared in library prosa.analysis.facts.job_index, line 308, characters 8-24
@prev_job_index_j
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_index Task Job H0 H arr_seq j) ->
       is_true (0 < @job_index Task Job H0 H arr_seq j) ->
       @job_index Task Job H0 H arr_seq (@prev_job Job Task H H0 arr_seq j) =
       @job_index Task Job H0 H arr_seq j - 1
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.prev_job_index_j : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        0 < Prosa.Model.Task.Arrivals.job_index arr_seq j →
          0 < Prosa.Model.Task.Arrivals.job_index arr_seq j →
            Prosa.Model.Task.Arrivals.job_index arr_seq (Prosa.Model.Task.Arrivals.prev_job arr_seq j) =
              Prosa.Model.Task.Arrivals.job_index arr_seq j - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_prev_job_index_j
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
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j) ->
       @eq Nat
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq
            (Prosa_Model_Task_Arrivals_prev_job Job
               inst_7 Task
               inst_3
               inst_10
               inst_14 arr_seq j))
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Task_Arrivals_job_index Task
               inst_3 Job
               inst_7
               inst_14
               inst_10 arr_seq j)
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
