# `job_arrival_separation_when_index_diff_is_k`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k`
- Lean: `Prosa.Analysis.Facts.Periodic.ArrivalSeparation.job_arrival_separation_when_index_diff_is_k`
- Certificate: `job_arrival_separation_when_index_diff_is_k_correspondence`

## Official Rocq

```coq
job_arrival_separation_when_index_diff_is_k :
forall {Task : TaskType} {H : PeriodicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_period Task H tsk) ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
@job_task Job Task H0 j1 = tsk ->
@job_task Job Task H0 j2 = tsk ->
forall k : nat,
@job_index Task Job H1 H0 arr_seq j1 + k = @job_index Task Job H1 H0 arr_seq j2 ->
is_true (@job_arrival Job H1 j1 < @job_arrival Job H1 j2) ->
exists n : nat,
  is_true (0 < n) /\ @job_arrival Job H1 j2 = @job_arrival Job H1 j1 + n * @task_period Task H tsk

job_arrival_separation_when_index_diff_is_k is not universe polymorphic
Arguments job_arrival_separation_when_index_diff_is_k {Task H Job H0 H1} arr_seq 
  H_valid_arrival_sequence tsk H_periodic_model H_valid_period j1 j2 H_j1_from_arr_seq 
  H_j2_from_arr_seq H_j1_of_task H_j2_of_task k%nat_scope H_index_difference_k H_job_arrival_lt
job_arrival_separation_when_index_diff_is_k is opaque
Expands to: Constant
            prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k
Declared in library prosa.analysis.facts.periodic.arrival_separation, line 81, characters 10-53
@job_arrival_separation_when_index_diff_is_k
     : forall (Task : TaskType) (H : PeriodicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_period Task H tsk) ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       @job_task Job Task H0 j1 = tsk ->
       @job_task Job Task H0 j2 = tsk ->
       forall k : nat,
       @job_index Task Job H1 H0 arr_seq j1 + k = @job_index Task Job H1 H0 arr_seq j2 ->
       is_true (@job_arrival Job H1 j1 < @job_arrival Job H1 j2) ->
       exists n : nat,
         is_true (0 < n) /\ @job_arrival Job H1 j2 = @job_arrival Job H1 j1 + n * @task_period Task H tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.ArrivalSeparation.job_arrival_separation_when_index_diff_is_k : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
          ∀ (j1 j2 : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
                Prosa.Model.Task.Concept.job_task j1 = tsk →
                  Prosa.Model.Task.Concept.job_task j2 = tsk →
                    ∀ (k : ℕ),
                      Prosa.Model.Task.Arrivals.job_index arr_seq j1 + k =
                          Prosa.Model.Task.Arrivals.job_index arr_seq j2 →
                        Prosa.Behavior.Job.job_arrival j1 < Prosa.Behavior.Job.job_arrival j2 →
                          ∃ n,
                            0 < n ∧
                              Prosa.Behavior.Job.job_arrival j2 =
                                Prosa.Behavior.Job.job_arrival j1 +
                                  n * Prosa.Model.Task.Arrival.Periodic.task_period tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_ArrivalSeparation_job_arrival_separation_when_index_diff_is_k
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
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
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       forall j1 j2 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j1 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j2 ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j1)
         tsk ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j2)
         tsk ->
       forall k : Nat,
       @eq Nat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Task_Arrivals_job_index Task
               inst_3 Job
               inst_10
               inst_17
               inst_13 arr_seq j1)
            k)
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_10
            inst_17
            inst_13 arr_seq j2) ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j1)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j2) ->
       Exists Nat
         (fun n : Nat =>
          And (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) n)
            (@eq Prosa_Behavior_Time_instant
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_10
                  inst_17 j2)
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_10
                     inst_17 j1)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) n
                     (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
                        inst_3
                        inst_6
                        tsk)))))
```
