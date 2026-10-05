# `subset_trigger_jobs`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.delay_propagation.subset_trigger_jobs`
- Lean: `Prosa.Analysis.Facts.DelayPropagation.subset_trigger_jobs`
- Certificate: `subset_trigger_jobs_correspondence`

## Official Rocq

```coq
subset_trigger_jobs :
forall {Task1 Task2 : TaskType} {Job1 Job2 : JobType} {H : JobTask Job1 Task1} {H0 : JobTask Job2 Task2}
  (JA1 : JobArrival Job1) (JA2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (task1_of : Equality.sort Task2 -> Equality.sort Task1)
  (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2)) (arrival_delay : Equality.sort Job2 -> duration)
  (delay_bound : Equality.sort Task2 -> duration) (ts2 : seq (Equality.sort Task2)),
@valid_delay_propagation_mapping Task1 Task2 Job1 Job2 H H0 JA1 JA2 job1_of task1_of delay_bound ts2 ->
forall arr_seq1 : arrival_sequence Job1,
@valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
  arrival_delay ts2 ->
@valid_arrival_sequence Job1 JA1 arr_seq1 ->
forall t1 t2 : instant,
is_true (t1 <= t2) ->
forall tsk2 : Equality.sort Task2,
is_true (tsk2 \in ts2) ->
{subset [seq job1_of j2
           | j2 <- @task_arrivals_between Job2 Task2 H0
                     (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2
                     t1 t2]
     <= @task_arrivals_between Job1 Task1 H arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2) t2}

subset_trigger_jobs is not universe polymorphic
Arguments subset_trigger_jobs {Task1 Task2 Job1 Job2 H H0} JA1 JA2
  (job1_of task1_of job2_of arrival_delay delay_bound)%function_scope ts2%seq_scope 
  H_valid_mapping arr_seq1 H_arr_seq_mapping H_valid_arr_seq t1 t2 H_ordered tsk2 
  H_in_ts x _
subset_trigger_jobs is opaque
Expands to: Constant prosa.analysis.facts.delay_propagation.subset_trigger_jobs
Declared in library prosa.analysis.facts.delay_propagation, line 232, characters 10-29
@subset_trigger_jobs
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
       @valid_arrival_sequence Job1 JA1 arr_seq1 ->
       forall t1 t2 : instant,
       is_true (t1 <= t2) ->
       forall tsk2 : Equality.sort Task2,
       is_true (tsk2 \in ts2) ->
       {subset [seq job1_of j2
                  | j2 <- @task_arrivals_between Job2 Task2 H0
                            (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of
                               arrival_delay)
                            tsk2 t1 t2]
            <= @task_arrivals_between Job1 Task1 H arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2) t2}
```

## Lean

```lean
@Prosa.Analysis.Facts.DelayPropagation.subset_trigger_jobs : ∀ {Task1 : Prosa.Model.Task.Concept.TaskType}
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
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq1 →
          ∀ (t1 t2 : Prosa.Behavior.Time.instant),
            t1 ≤ t2 →
              ∀ (tsk2 : Task2),
                decide (tsk2 ∈ ts2) = true →
                  ∀ (j1 : Job1),
                    decide
                          (j1 ∈
                            List.map job1_of
                              (Prosa.Model.Task.Arrivals.task_arrivals_between
                                (Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence JA1 job1_of
                                  arr_seq1 job2_of arrival_delay)
                                tsk2 t1 t2)) =
                        true →
                      decide
                          (j1 ∈
                            Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq1 (task1_of tsk2)
                              (t1 - delay_bound tsk2) t2) =
                        true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_DelayPropagation_subset_trigger_jobs
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
       forall j1 : Job1,
       @eq Bool
         (Decidable_decide
            (Membership_mem Job1 (List Job1) (List_instMembership Job1)
               (List_map Job2 Job1 job1_of
                  (Prosa_Model_Task_Arrivals_task_arrivals_between Job2
                     inst_15 Task2
                     inst_7
                     inst_22
                     (Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2
                        inst_12
                        inst_15 JA1
                        job1_of arr_seq1 job2_of arrival_delay)
                     tsk2 t1 t2))
               j1)
            (List_instDecidableMemOfLawfulBEq Job1
               (instBEqOfDecidableEq Job1
                  inst_12)
               (instLawfulBEq Job1
                  inst_12)
               j1
               (List_map Job2 Job1 job1_of
                  (Prosa_Model_Task_Arrivals_task_arrivals_between Job2
                     inst_15 Task2
                     inst_7
                     inst_22
                     (Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2
                        inst_12
                        inst_15 JA1
                        job1_of arr_seq1 job2_of arrival_delay)
                     tsk2 t1 t2))))
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job1 (List Job1) (List_instMembership Job1)
               (Prosa_Model_Task_Arrivals_task_arrivals_between Job1
                  inst_12 Task1
                  inst_4
                  inst_18 arr_seq1
                  (task1_of tsk2)
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t1
                     (delay_bound tsk2))
                  t2)
               j1)
            (List_instDecidableMemOfLawfulBEq Job1
               (instBEqOfDecidableEq Job1
                  inst_12)
               (instLawfulBEq Job1
                  inst_12)
               j1
               (Prosa_Model_Task_Arrivals_task_arrivals_between Job1
                  inst_12 Task1
                  inst_4
                  inst_18 arr_seq1
                  (task1_of tsk2)
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t1
                     (delay_bound tsk2))
                  t2)))
         Bool_true
```
