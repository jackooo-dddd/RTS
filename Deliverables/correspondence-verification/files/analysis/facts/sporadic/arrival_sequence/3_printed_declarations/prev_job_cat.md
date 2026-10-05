# `prev_job_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.prev_job_cat`
- Certificate: `prev_job_cat_correspondence`

## Official Rocq

```coq
prev_job_cat :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
forall j1 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@job_task Job Task H0 j1 = tsk ->
is_true (0 < @job_index Task Job H1 H0 arr_seq j1) ->
@task_arrivals_up_to_job_arrival Job Task H0 H1 arr_seq (@prev_job Job Task H0 H1 arr_seq j1) ++ [:: j1] =
@task_arrivals_up_to_job_arrival Job Task H0 H1 arr_seq j1

prev_job_cat is not universe polymorphic
Arguments prev_job_cat {Task H Job H0 H1} arr_seq H_valid_arrival_sequence tsk H_sporadic_model
  H_valid_inter_min_arrival j1 H_j1_from_arrival_sequence H_j1_task _
prev_job_cat is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat
Declared in library prosa.analysis.facts.sporadic.arrival_sequence, line 132, characters 8-20
@prev_job_cat
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
       forall j1 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @job_task Job Task H0 j1 = tsk ->
       is_true (0 < @job_index Task Job H1 H0 arr_seq j1) ->
       @task_arrivals_up_to_job_arrival Job Task H0 H1 arr_seq (@prev_job Job Task H0 H1 arr_seq j1) ++
       [:: j1] = @task_arrivals_up_to_job_arrival Job Task H0 H1 arr_seq j1
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalSequence.prev_job_cat : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true →
          ∀ (j1 : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
              Prosa.Model.Task.Concept.job_task j1 = tsk →
                0 < Prosa.Model.Task.Arrivals.job_index arr_seq j1 →
                  Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq
                        (Prosa.Model.Task.Arrivals.prev_job arr_seq j1) ++
                      [j1] =
                    Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalSequence_prev_job_cat
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3)
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
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall tsk : Task,
       Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       forall j1 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j1 ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j1)
         tsk ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_10
            inst_17
            inst_13 arr_seq j1) ->
       @eq (List Job)
         (HAppend_hAppend (List Job) (List Job) (List Job)
            (instHAppendOfAppend (List Job) (List_instAppend Job))
            (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
               inst_10 Task
               inst_3
               inst_13
               inst_17 arr_seq
               (Prosa_Model_Task_Arrivals_prev_job Job
                  inst_10 Task
                  inst_3
                  inst_13
                  inst_17 arr_seq
                  j1))
            (List_cons Job j1 (List_nil Job)))
         (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
            inst_10 Task
            inst_3
            inst_13
            inst_17 arr_seq j1)
```
