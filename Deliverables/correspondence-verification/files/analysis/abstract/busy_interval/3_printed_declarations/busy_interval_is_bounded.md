# `busy_interval_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.busy_interval_is_bounded`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.busy_interval_is_bounded`
- Certificate: `busy_interval_is_bounded_correspondence`

## Official Rocq

```coq
busy_interval_is_bounded :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall {H3 : Interference Job} {H4 : InterferingWorkload Job},
@no_speculative_execution Job H3 H4 ->
forall arr_seq : arrival_sequence Job,
@consistent_arrival_times Job H1 arr_seq ->
@arrival_sequence_uniq Job arr_seq ->
forall (tsk : Equality.sort Task) (sched : @schedule Job PState),
@work_conserving Job H1 H2 PState arr_seq sched H3 H4 ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (@job_cost_positive Job H2 j) ->
forall t_busy : instant,
is_true (@pending Job PState sched H2 H1 j t_busy) ->
forall t1 : instant,
@busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t_busy.+1 ->
forall δ : duration,
is_true (0 < δ) ->
is_true
  (@workload_of_job Job H2 arr_seq j t1 (t1 + δ) + @cumulative_interfering_workload Job H4 j t1 (t1 + δ) <= δ) ->
exists t2 : nat,
  is_true (t_busy < t2) /\ is_true (t2 <= t1 + δ) /\ @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2

busy_interval_is_bounded is not universe polymorphic
Arguments busy_interval_is_bounded {Task Job H0 H1 H2 PState} H_unit_service_proc_model 
  {H3 H4} H_no_speculative_exec arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 
  tsk sched H_work_conserving H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  j H_from_arrival_sequence H_job_task H_job_cost_positive t_busy H_j_is_pending 
  t1 H_is_busy_prefix δ H_δ_positive H_workload_is_bounded
busy_interval_is_bounded is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.busy_interval_is_bounded
Declared in library prosa.analysis.abstract.busy_interval, line 490, characters 12-36
@busy_interval_is_bounded
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @no_speculative_execution Job H3 H4 ->
       forall arr_seq : arrival_sequence Job,
       @consistent_arrival_times Job H1 arr_seq ->
       @arrival_sequence_uniq Job arr_seq ->
       forall (tsk : Equality.sort Task) (sched : @schedule Job PState),
       @work_conserving Job H1 H2 PState arr_seq sched H3 H4 ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t_busy : instant,
       is_true (@pending Job PState sched H2 H1 j t_busy) ->
       forall t1 : instant,
       @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t_busy.+1 ->
       forall δ : duration,
       is_true (0 < δ) ->
       is_true
         (@workload_of_job Job H2 arr_seq j t1 (t1 + δ) +
          @cumulative_interfering_workload Job H4 j t1 (t1 + δ) <= δ) ->
       exists t2 : nat,
         is_true (t_busy < t2) /\
         is_true (t2 <= t1 + δ) /\ @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.busy_interval_is_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
      [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
      Prosa.Analysis.Abstract.Definitions.no_speculative_execution →
        ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
          Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
            Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
              ∀ (tsk : Task) (sched : Prosa.Behavior.Schedule.schedule PState),
                Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                      ∀ (j : Job),
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                          Prosa.Model.Task.Concept.job_of_task tsk j = true →
                            Prosa.Model.Job.Properties.job_cost_positive j = true →
                              ∀ (t_busy : Prosa.Behavior.Time.instant),
                                Prosa.Behavior.Service.pending sched j t_busy = true →
                                  ∀ (t1 : Prosa.Behavior.Time.instant),
                                    Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 (t_busy + 1) →
                                      ∀ (δ : Prosa.Behavior.Time.duration),
                                        0 < δ →
                                          Prosa.Model.Aggregate.Workload.workload_of_job arr_seq j t1 (t1 + δ) +
                                                Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload j t1
                                                  (t1 + δ) ≤
                                              δ →
                                            ∃ t2,
                                              t_busy < t2 ∧
                                                t2 ≤ t1 + δ ∧
                                                  Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_busy_interval_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_7 PState ->
       forall
         (inst_27 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_30 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_no_speculative_execution Job
         inst_7
         inst_27
         inst_30 ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_7
         inst_14 arr_seq ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_7 arr_seq ->
       forall (tsk : Task)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_27
         inst_30
         inst_14
         inst_17 PState arr_seq sched ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState sched
         inst_17 ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t_busy : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_7 PState sched
            inst_17
            inst_14 j t_busy)
         Bool_true ->
       forall t1 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         inst_27
         inst_30
         inst_14
         inst_17 PState sched j t1
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t_busy
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       forall _UU03b4_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) _UU03b4_ ->
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_Workload_workload_of_job Job
               inst_7
               inst_17 arr_seq j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU03b4_))
            (Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
               inst_7
               inst_30 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU03b4_)))
         _UU03b4_ ->
       Exists Nat
         (fun t2 : Nat =>
          And (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t_busy t2)
            (And
               (LE_le_inst1 Nat instLENat t2
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     _UU03b4_))
               (Prosa_Analysis_Abstract_Definitions_busy_interval Job
                  inst_7
                  inst_27
                  inst_30
                  inst_14
                  inst_17 PState sched j
                  t1 t2)))
```
