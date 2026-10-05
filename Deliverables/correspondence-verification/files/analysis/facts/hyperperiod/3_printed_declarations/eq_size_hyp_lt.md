# `eq_size_hyp_lt`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.eq_size_hyp_lt`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.eq_size_hyp_lt`
- Certificate: `eq_size_hyp_lt_correspondence`

## Official Rocq

```coq
eq_size_hyp_lt :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall (ts : TaskSet (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_offset Task H Job H1 H2 arr_seq tsk ->
is_true (@valid_period Task H0 tsk) ->
@respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
@infinite_jobs Task Job H1 H2 arr_seq ->
forall n1 n2 : nat,
is_true (n1 <= n2) ->
@size (Equality.sort Job)
  (@jobs_in_hyperperiod Task H0 Job H1 ts arr_seq (n1 * @hyperperiod Task H0 ts + @max_task_offset Task H ts)
     tsk) =
@size (Equality.sort Job)
  (@jobs_in_hyperperiod Task H0 Job H1 ts arr_seq (n2 * @hyperperiod Task H0 ts + @max_task_offset Task H ts)
     tsk)

eq_size_hyp_lt is not universe polymorphic
Arguments eq_size_hyp_lt {Task H H0 Job H1 H2} arr_seq H_valid_arrival_sequence ts 
  tsk H_task_in_ts H_valid_offset H_valid_period H_periodic_task H_infinite_jobs 
  (n1 n2)%nat_scope _
eq_size_hyp_lt is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.eq_size_hyp_lt
Declared in library prosa.analysis.facts.hyperperiod, line 130, characters 8-22
@eq_size_hyp_lt
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall (ts : TaskSet (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_offset Task H Job H1 H2 arr_seq tsk ->
       is_true (@valid_period Task H0 tsk) ->
       @respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
       @infinite_jobs Task Job H1 H2 arr_seq ->
       forall n1 n2 : nat,
       is_true (n1 <= n2) ->
       @size (Equality.sort Job)
         (@jobs_in_hyperperiod Task H0 Job H1 ts arr_seq
            (n1 * @hyperperiod Task H0 ts + @max_task_offset Task H ts) tsk) =
       @size (Equality.sort Job)
         (@jobs_in_hyperperiod Task H0 Job H1 ts arr_seq
            (n2 * @hyperperiod Task H0 ts + @max_task_offset Task H ts) tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.eq_size_hyp_lt : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task]
  [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task) (tsk : Task),
      decide (tsk ∈ ts) = true →
        Prosa.Model.Task.Offset.valid_offset arr_seq tsk →
          Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
            Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
              Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs arr_seq →
                ∀ (n1 n2 : ℕ),
                  n1 ≤ n2 →
                    (Prosa.Analysis.Definitions.Hyperperiod.jobs_in_hyperperiod ts arr_seq
                          (n1 * Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts +
                            Prosa.Model.Task.Offset.max_task_offset ts)
                          tsk).length =
                      (Prosa.Analysis.Definitions.Hyperperiod.jobs_in_hyperperiod ts arr_seq
                          (n2 * Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts +
                            Prosa.Model.Task.Offset.max_task_offset ts)
                          tsk).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_eq_size_hyp_lt
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       forall (ts : Prosa_Model_Task_Concept_TaskSet Task) (tsk : Task),
       @eq Bool
         (Decidable_decide
            (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3) tsk
               ts))
         Bool_true ->
       Prosa_Model_Task_Offset_valid_offset Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_20 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_9 tsk)
         Bool_true ->
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_9 Job
         inst_13
         inst_16
         inst_20 arr_seq tsk ->
       Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs Task
         inst_3 Job
         inst_13
         inst_16
         inst_20 arr_seq ->
       forall n1 n2 : Nat,
       LE_le_inst1 Nat instLENat n1 n2 ->
       @eq Nat
         (List_length Job
            (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
               inst_3
               inst_9 Job
               inst_13
               inst_16 ts arr_seq
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) n1
                     (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                        inst_3
                        inst_9 ts))
                  (Prosa_Model_Task_Offset_max_task_offset Task
                     inst_3
                     inst_6 ts))
               tsk))
         (List_length Job
            (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
               inst_3
               inst_9 Job
               inst_13
               inst_16 ts arr_seq
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) n2
                     (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                        inst_3
                        inst_9 ts))
                  (Prosa_Model_Task_Offset_max_task_offset Task
                     inst_3
                     inst_6 ts))
               tsk))
```
