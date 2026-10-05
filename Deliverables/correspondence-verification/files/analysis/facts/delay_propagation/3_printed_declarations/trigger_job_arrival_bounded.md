# `trigger_job_arrival_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.delay_propagation.trigger_job_arrival_bounded`
- Lean: `Prosa.Analysis.Facts.DelayPropagation.trigger_job_arrival_bounded`
- Certificate: `trigger_job_arrival_bounded_correspondence`

## Official Rocq

```coq
trigger_job_arrival_bounded :
forall {Task2 : TaskType} {Job1 Job2 : JobType} {H0 : JobTask Job2 Task2} (JA1 : JobArrival Job1)
  (JA2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2)) (arrival_delay : Equality.sort Job2 -> duration)
  (delay_bound : Equality.sort Task2 -> duration) (ts2 : seq (Equality.sort Task2))
  (arr_seq1 : arrival_sequence Job1),
@valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
  arrival_delay ts2 ->
forall t1 t2 : instant,
is_true (t1 <= t2) ->
forall tsk2 : Equality.sort Task2,
is_true (tsk2 \in ts2) ->
forall j1 : Equality.sort Job1,
is_true
  (j1
     \in [seq job1_of j2
            | j2 <- @task_arrivals_between Job2 Task2 H0
                      (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of arrival_delay)
                      tsk2 t1 t2]) ->
is_true (t1 - delay_bound tsk2 <= @job_arrival Job1 JA1 j1 < t2)

trigger_job_arrival_bounded is not universe polymorphic
Arguments trigger_job_arrival_bounded {Task2 Job1 Job2 H0} JA1 JA2
  (job1_of job2_of arrival_delay delay_bound)%function_scope ts2%seq_scope arr_seq1 
  H_arr_seq_mapping t1 t2 H_ordered tsk2 H_in_ts j1 _
trigger_job_arrival_bounded is opaque
Expands to: Constant prosa.analysis.facts.delay_propagation.trigger_job_arrival_bounded
Declared in library prosa.analysis.facts.delay_propagation, line 205, characters 10-37
@trigger_job_arrival_bounded
     : forall (Task2 : TaskType) (Job1 Job2 : JobType) (H0 : JobTask Job2 Task2) 
         (JA1 : JobArrival Job1) (JA2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
         (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2))
         (arrival_delay : Equality.sort Job2 -> duration) (delay_bound : Equality.sort Task2 -> duration)
         (ts2 : seq (Equality.sort Task2)) (arr_seq1 : arrival_sequence Job1),
       @valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
         arrival_delay ts2 ->
       forall t1 t2 : instant,
       is_true (t1 <= t2) ->
       forall tsk2 : Equality.sort Task2,
       is_true (tsk2 \in ts2) ->
       forall j1 : Equality.sort Job1,
       is_true
         (j1
            \in [seq job1_of j2
                   | j2 <- @task_arrivals_between Job2 Task2 H0
                             (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of
                                arrival_delay)
                             tsk2 t1 t2]) ->
       is_true (t1 - delay_bound tsk2 <= @job_arrival Job1 JA1 j1 < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.DelayPropagation.trigger_job_arrival_bounded : ∀ {Task2 : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task2] {Job1 : Prosa.Behavior.Job.JobType} {Job2 : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job1] [inst_2 : DecidableEq Job2] [inst_3 : Prosa.Model.Task.Concept.JobTask Job2 Task2]
  [JA1 : Prosa.Behavior.Job.JobArrival Job1] [JA2 : Prosa.Behavior.Job.JobArrival Job2] (job1_of : Job2 → Job1)
  (job2_of : Job1 → List Job2) (arrival_delay : Job2 → Prosa.Behavior.Time.duration)
  (delay_bound : Task2 → Prosa.Behavior.Time.duration) (ts2 : List Task2)
  (arr_seq1 : Prosa.Behavior.Arrival_sequence.arrival_sequence Job1),
  Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1
      job2_of arrival_delay ts2 →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      t1 ≤ t2 →
        ∀ (tsk2 : Task2),
          decide (tsk2 ∈ ts2) = true →
            ∀ (j1 : Job1),
              decide
                    (j1 ∈
                      List.map job1_of
                        (Prosa.Model.Task.Arrivals.task_arrivals_between
                          (Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence JA1 job1_of arr_seq1
                            job2_of arrival_delay)
                          tsk2 t1 t2)) =
                  true →
                (decide (t1 - delay_bound tsk2 ≤ Prosa.Behavior.Job.job_arrival j1) &&
                    decide (Prosa.Behavior.Job.job_arrival j1 < t2)) =
                  true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_DelayPropagation_trigger_job_arrival_bounded
     : forall (Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_8 : DecidableEq Job1)
         (inst_11 : DecidableEq Job2)
         (inst_14 : 
          Prosa_Model_Task_Concept_JobTask Job2
            inst_11 Task2
            inst_3)
         (JA1 : Prosa_Behavior_Job_JobArrival Job1
                  inst_8)
         (JA2 : Prosa_Behavior_Job_JobArrival Job2
                  inst_11)
         (job1_of : Job2 -> Job1) (job2_of : Job1 -> List Job2)
         (arrival_delay : Job2 -> Prosa_Behavior_Time_duration)
         (delay_bound : Task2 -> Prosa_Behavior_Time_duration) (ts2 : List Task2)
         (arr_seq1 : Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
                       inst_8),
       Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping Task2
         inst_3 Job1 Job2
         inst_8
         inst_11
         inst_14 JA1 JA2 job1_of
         delay_bound arr_seq1 job2_of arrival_delay ts2 ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall tsk2 : Task2,
       @eq Bool
         (Decidable_decide (Membership_mem Task2 (List Task2) (List_instMembership Task2) ts2 tsk2)
            (List_instDecidableMemOfLawfulBEq Task2
               (instBEqOfDecidableEq Task2
                  inst_3)
               (instLawfulBEq Task2
                  inst_3)
               tsk2 ts2))
         Bool_true ->
       forall j1 : Job1,
       @eq Bool
         (Decidable_decide
            (Membership_mem Job1 (List Job1) (List_instMembership Job1)
               (List_map Job2 Job1 job1_of
                  (Prosa_Model_Task_Arrivals_task_arrivals_between Job2
                     inst_11 Task2
                     inst_3
                     inst_14
                     (Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2
                        inst_8
                        inst_11 JA1
                        job1_of arr_seq1 job2_of arrival_delay)
                     tsk2 t1 t2))
               j1)
            (List_instDecidableMemOfLawfulBEq Job1
               (instBEqOfDecidableEq Job1
                  inst_8)
               (instLawfulBEq Job1 inst_8)
               j1
               (List_map Job2 Job1 job1_of
                  (Prosa_Model_Task_Arrivals_task_arrivals_between Job2
                     inst_11 Task2
                     inst_3
                     inst_14
                     (Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2
                        inst_8
                        inst_11 JA1
                        job1_of arr_seq1 job2_of arrival_delay)
                     tsk2 t1 t2))))
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t1
                     (delay_bound tsk2))
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job1
                     inst_8 JA1 j1))
               (Nat_decLe
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t1
                     (delay_bound tsk2))
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job1
                     inst_8 JA1 j1)))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job1
                     inst_8 JA1 j1)
                  t2)
               (Nat_decLt
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job1
                     inst_8 JA1 j1)
                  t2)))
         Bool_true
```
