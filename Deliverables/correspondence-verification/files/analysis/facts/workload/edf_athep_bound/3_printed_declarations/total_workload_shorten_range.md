# `total_workload_shorten_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range`
- Lean: `Prosa.Analysis.Facts.Workload.EdfAthepBound.total_workload_shorten_range`
- Certificate: `total_workload_shorten_range_correspondence`

## Official Rocq

```coq
total_workload_shorten_range :
forall {Task : TaskType} {H0 : TaskDeadline Task} {Job : JobType} {H2 : JobTask Job Task}
  {H3 : JobArrival Job} {H4 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H2 tsk j) ->
is_true (@job_cost_positive Job H4 j) ->
forall t1 t2 Δ : duration,
is_true (t1 + Δ < t2) ->
forall tsk_o : Equality.sort Task,
is_true (tsk_o \in ts) ->
is_true (tsk_o != tsk) ->
is_true
  (@job_arrival Job H3 j - t1 + 1 + [eta @task_deadline Task H0] tsk - [eta @task_deadline Task H0] tsk_o <=
   Δ) ->
is_true
  (@workload_of_jobs Job H4
     ((fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @EDF Job (@job_deadline_from_task_deadline Job Task H0 H3 H2) jo j &&
       (@job_task Job Task H2 jo == tsk0)) tsk_o)
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   @workload_of_jobs Job H4
     ((fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @EDF Job (@job_deadline_from_task_deadline Job Task H0 H3 H2) jo j &&
       (@job_task Job Task H2 jo == tsk0)) tsk_o)
     (@arrivals_between Job arr_seq t1
        (t1 +
         (@job_arrival Job H3 j - t1 + 1 + [eta @task_deadline Task H0] tsk -
          [eta @task_deadline Task H0] tsk_o))))

total_workload_shorten_range is not universe polymorphic
Arguments total_workload_shorten_range {Task H0 Job H2 H3 H4} arr_seq H_valid_arrival_sequence 
  ts%seq_scope tsk j H_job_of_tsk H_job_cost_positive t1 t2 Δ H_Δ_in_busy tsk_o H_tsko_in_ts 
  H_neq H_Δ_ge
total_workload_shorten_range is opaque
Expands to: Constant prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range
Declared in library prosa.analysis.facts.workload.edf_athep_bound, line 109, characters 12-40
@total_workload_shorten_range
     : forall (Task : TaskType) (H0 : TaskDeadline Task) (Job : JobType) (H2 : JobTask Job Task)
         (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H2 tsk j) ->
       is_true (@job_cost_positive Job H4 j) ->
       forall t1 t2 Δ : duration,
       is_true (t1 + Δ < t2) ->
       forall tsk_o : Equality.sort Task,
       is_true (tsk_o \in ts) ->
       is_true (tsk_o != tsk) ->
       is_true
         (@job_arrival Job H3 j - t1 + 1 + @task_deadline Task H0 tsk - @task_deadline Task H0 tsk_o <= Δ) ->
       is_true
         (@workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @EDF Job (@job_deadline_from_task_deadline Job Task H0 H3 H2) jo j &&
             (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
          @workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @EDF Job (@job_deadline_from_task_deadline Job Task H0 H3 H2) jo j &&
             (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1
               (t1 +
                (@job_arrival Job H3 j - t1 + 1 + @task_deadline Task H0 tsk - @task_deadline Task H0 tsk_o))))
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.EdfAthepBound.total_workload_shorten_range : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : List Task) (tsk : Task) (j : Job),
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Model.Job.Properties.job_cost_positive j = true →
          ∀ (t1 t2 Δ : Prosa.Behavior.Time.duration),
            t1 + Δ < t2 →
              ∀ (tsk_o : Task),
                decide (tsk_o ∈ ts) = true →
                  decide (tsk_o ≠ tsk) = true →
                    Prosa.Behavior.Job.job_arrival j - t1 + 1 + Prosa.Model.Task.Concept.task_deadline tsk -
                          Prosa.Model.Task.Concept.task_deadline tsk_o ≤
                        Δ →
                      Prosa.Model.Aggregate.Workload.workload_of_jobs
                          (fun jo =>
                            Prosa.Model.Priority.Definitions.hep_job jo j &&
                              decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) ≤
                        Prosa.Model.Aggregate.Workload.workload_of_jobs
                          (fun jo =>
                            Prosa.Model.Priority.Definitions.hep_job jo j &&
                              decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                            (t1 +
                              (Prosa.Behavior.Job.job_arrival j - t1 + 1 + Prosa.Model.Task.Concept.task_deadline tsk -
                                Prosa.Model.Task.Concept.task_deadline tsk_o)))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_EdfAthepBound_total_workload_shorten_range
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
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
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall (ts : List Task) (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_10 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_10
            inst_20 j)
         Bool_true ->
       forall t1 t2 _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1 _UU0394_)
         t2 ->
       forall tsk_o : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk_o)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk_o ts))
         Bool_true ->
       @eq Bool
         (Decidable_decide (Ne Task tsk_o tsk)
            (instDecidableNot (@eq Task tsk_o tsk)
               (inst_3 tsk_o tsk)))
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_10
                        inst_17 j)
                     t1)
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
               (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                  inst_3
                  inst_6 tsk))
            (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
               inst_3
               inst_6 tsk_o))
         _UU0394_ ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_10
            inst_20
            (fun jo : Job =>
             Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_10
                  (Prosa_Model_Priority_Edf_EDF Job
                     inst_10
                     (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                        inst_10
                        inst_3
                        inst_6
                        inst_17
                        inst_13))
                  jo j)
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10
                        Task inst_3
                        inst_13 jo)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10
                        Task inst_3
                        inst_13 jo)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_10 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                  _UU0394_)))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_10
            inst_20
            (fun jo : Job =>
             Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_10
                  (Prosa_Model_Priority_Edf_EDF Job
                     inst_10
                     (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                        inst_10
                        inst_3
                        inst_6
                        inst_17
                        inst_13))
                  jo j)
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10
                        Task inst_3
                        inst_13 jo)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10
                        Task inst_3
                        inst_13 jo)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_10 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                           Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_10
                                 inst_17
                                 j)
                              t1)
                           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
                        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                           inst_3
                           inst_6
                           tsk))
                     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                        inst_3
                        inst_6
                        tsk_o)))))
```
