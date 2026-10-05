# `trigger_job_size`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.delay_propagation.trigger_job_size`
- Lean: `Prosa.Analysis.Facts.DelayPropagation.trigger_job_size`
- Certificate: `trigger_job_size_correspondence`

## Official Rocq

```coq
trigger_job_size :
forall {Task1 Task2 : TaskType} {Job1 Job2 : JobType} {H : JobTask Job1 Task1} {H0 : JobTask Job2 Task2}
  (JA1 : JobArrival Job1) (JA2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (task1_of : Equality.sort Task2 -> Equality.sort Task1)
  (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2)) (arrival_delay : Equality.sort Job2 -> duration)
  (delay_bound : Equality.sort Task2 -> duration) (ts2 : seq (Equality.sort Task2)),
@valid_delay_propagation_mapping Task1 Task2 Job1 Job2 H H0 JA1 JA2 job1_of task1_of delay_bound ts2 ->
forall arr_seq1 : arrival_sequence Job1,
@valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
  arrival_delay ts2 ->
(forall tsk1 : Equality.sort Task1,
 is_true (tsk1 \in [seq task1_of tsk2 | tsk2 <- ts2]) ->
 forall j1 : Equality.sort Job1,
 @job_task Job1 Task1 H j1 = tsk1 -> is_true (@size (Equality.sort Job2) (job2_of j1) <= 1)) ->
@valid_arrival_sequence Job1 JA1 arr_seq1 ->
forall t1 t2 : instant,
is_true (t1 <= t2) ->
forall tsk2 : Equality.sort Task2,
is_true (tsk2 \in ts2) ->
is_true
  (@size (Equality.sort Job1)
     [seq job1_of j2
        | j2 <- @task_arrivals_between Job2 Task2 H0
                  (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1
                  t2] <=
   @size (Equality.sort Job1)
     (@task_arrivals_between Job1 Task1 H arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2) t2))

trigger_job_size is not universe polymorphic
Arguments trigger_job_size {Task1 Task2 Job1 Job2 H H0} JA1 JA2
  (job1_of task1_of job2_of arrival_delay delay_bound)%function_scope ts2%seq_scope 
  H_valid_mapping arr_seq1 H_arr_seq_mapping H_job2_of_singleton%function_scope H_valid_arr_seq 
  t1 t2 H_ordered tsk2 H_in_ts
trigger_job_size is opaque
Expands to: Constant prosa.analysis.facts.delay_propagation.trigger_job_size
Declared in library prosa.analysis.facts.delay_propagation, line 281, characters 14-30
@trigger_job_size
     : forall (Task1 Task2 : TaskType) (Job1 Job2 : JobType) (H : JobTask Job1 Task1)
         (H0 : JobTask Job2 Task2) (JA1 : JobArrival Job1) (JA2 : JobArrival Job2)
         (job1_of : Equality.sort Job2 -> Equality.sort Job1)
         (task1_of : Equality.sort Task2 -> Equality.sort Task1)
         (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2))
         (arrival_delay : Equality.sort Job2 -> duration) (delay_bound : Equality.sort Task2 -> duration)
         (ts2 : seq (Equality.sort Task2)),
       @valid_delay_propagation_mapping Task1 Task2 Job1 Job2 H H0 JA1 JA2 job1_of task1_of delay_bound ts2 ->
       forall arr_seq1 : arrival_sequence Job1,
       @valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
         arrival_delay ts2 ->
       (forall tsk1 : Equality.sort Task1,
        is_true (tsk1 \in [seq task1_of tsk2 | tsk2 <- ts2]) ->
        forall j1 : Equality.sort Job1,
        @job_task Job1 Task1 H j1 = tsk1 -> is_true (@size (Equality.sort Job2) (job2_of j1) <= 1)) ->
       @valid_arrival_sequence Job1 JA1 arr_seq1 ->
       forall t1 t2 : instant,
       is_true (t1 <= t2) ->
       forall tsk2 : Equality.sort Task2,
       is_true (tsk2 \in ts2) ->
       is_true
         (@size (Equality.sort Job1)
            [seq job1_of j2
               | j2 <- @task_arrivals_between Job2 Task2 H0
                         (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of arrival_delay)
                         tsk2 t1 t2] <=
          @size (Equality.sort Job1)
            (@task_arrivals_between Job1 Task1 H arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2) t2))
```

## Lean

```lean
@Prosa.Analysis.Facts.DelayPropagation.trigger_job_size : ∀ {Task1 : Prosa.Model.Task.Concept.TaskType}
  {Task2 : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task1] [inst_1 : DecidableEq Task2]
  {Job1 : Prosa.Behavior.Job.JobType} {Job2 : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job1]
  [inst_3 : DecidableEq Job2] [inst_4 : Prosa.Model.Task.Concept.JobTask Job1 Task1]
  [inst_5 : Prosa.Model.Task.Concept.JobTask Job2 Task2] [JA1 : Prosa.Behavior.Job.JobArrival Job1]
  [JA2 : Prosa.Behavior.Job.JobArrival Job2] (job1_of : Job2 → Job1) (task1_of : Task2 → Task1)
  (job2_of : Job1 → List Job2) (arrival_delay : Job2 → Prosa.Behavior.Time.duration)
  (delay_bound : Task2 → Prosa.Behavior.Time.duration) (ts2 : List Task2),
  Prosa.Analysis.Definitions.DelayPropagation.valid_delay_propagation_mapping JA1 JA2 job1_of task1_of delay_bound ts2 →
    ∀ (arr_seq1 : Prosa.Behavior.Arrival_sequence.arrival_sequence Job1),
      Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1
          job2_of arrival_delay ts2 →
        (∀ (tsk1 : Task1),
            decide (tsk1 ∈ List.map task1_of ts2) = true →
              ∀ (j1 : Job1), Prosa.Model.Task.Concept.job_task j1 = tsk1 → (job2_of j1).length ≤ 1) →
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq1 →
            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
              t1 ≤ t2 →
                ∀ (tsk2 : Task2),
                  decide (tsk2 ∈ ts2) = true →
                    (List.map job1_of
                          (Prosa.Model.Task.Arrivals.task_arrivals_between
                            (Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence JA1 job1_of
                              arr_seq1 job2_of arrival_delay)
                            tsk2 t1 t2)).length ≤
                      (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2)
                          t2).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_DelayPropagation_trigger_job_size
     : forall (Task1 Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : DecidableEq Task1)
         (inst_7 : DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_12 : DecidableEq Job1)
         (inst_15 : DecidableEq Job2)
         (inst_18 : 
          Prosa_Model_Task_Concept_JobTask Job1
            inst_12 Task1
            inst_4)
         (inst_22 : 
          Prosa_Model_Task_Concept_JobTask Job2
            inst_15 Task2
            inst_7)
         (JA1 : Prosa_Behavior_Job_JobArrival Job1
                  inst_12)
         (JA2 : Prosa_Behavior_Job_JobArrival Job2
                  inst_15)
         (job1_of : Job2 -> Job1) (task1_of : Task2 -> Task1) (job2_of : Job1 -> List Job2)
         (arrival_delay : Job2 -> Prosa_Behavior_Time_duration)
         (delay_bound : Task2 -> Prosa_Behavior_Time_duration) (ts2 : List Task2),
       Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping Task1 Task2
         inst_4
         inst_7 Job1 Job2
         inst_12
         inst_15
         inst_18
         inst_22 JA1 JA2 job1_of task1_of
         delay_bound ts2 ->
       forall
         arr_seq1 : Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
                      inst_12,
       Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping Task2
         inst_7 Job1 Job2
         inst_12
         inst_15
         inst_22 JA1 JA2 job1_of
         delay_bound arr_seq1 job2_of arrival_delay ts2 ->
       (forall tsk1 : Task1,
        @eq Bool
          (Decidable_decide
             (Membership_mem Task1 (List Task1) (List_instMembership Task1)
                (List_map Task2 Task1 task1_of ts2) tsk1)
             (List_instDecidableMemOfLawfulBEq Task1
                (instBEqOfDecidableEq Task1
                   inst_4)
                (instLawfulBEq Task1
                   inst_4)
                tsk1 (List_map Task2 Task1 task1_of ts2)))
          Bool_true ->
        forall j1 : Job1,
        @eq Task1
          (Prosa_Model_Task_Concept_JobTask_job_task Job1
             inst_12 Task1
             inst_4
             inst_18 j1)
          tsk1 ->
        LE_le_inst1 Nat instLENat (List_length Job2 (job2_of j1)) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job1
         inst_12 JA1 arr_seq1 ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall tsk2 : Task2,
       @eq Bool
         (Decidable_decide (Membership_mem Task2 (List Task2) (List_instMembership Task2) ts2 tsk2)
            (List_instDecidableMemOfLawfulBEq Task2
               (instBEqOfDecidableEq Task2
                  inst_7)
               (instLawfulBEq Task2
                  inst_7)
               tsk2 ts2))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (List_length Job1
            (List_map Job2 Job1 job1_of
               (Prosa_Model_Task_Arrivals_task_arrivals_between Job2
                  inst_15 Task2
                  inst_7
                  inst_22
                  (Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2
                     inst_12
                     inst_15 JA1 job1_of
                     arr_seq1 job2_of arrival_delay)
                  tsk2 t1 t2)))
         (List_length Job1
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job1
               inst_12 Task1
               inst_4
               inst_18 arr_seq1
               (task1_of tsk2)
               (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t1
                  (delay_bound tsk2))
               t2))
```
