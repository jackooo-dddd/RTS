# `bound_on_hep_workload`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload`
- Lean: `Prosa.Analysis.Facts.Priority.FifoAhepBound.bound_on_hep_workload`
- Certificate: `bound_on_hep_workload_correspondence`

## Official Rocq

```coq
bound_on_hep_workload :
forall {Task : TaskType} {H : TaskCost Task} {H0 : curves.MaxArrivals Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobCost Job} {H3 : JobArrival Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H1 H2 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@curves.taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
@curves.valid_taskset_arrival_curve Task ts (@curves.max_arrivals Task H0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H3 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall j : Equality.sort Job,
is_true (@job_of_task Job Task H1 tsk j) ->
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval Job H3 H2 PState arr_seq sched (@fifo.FIFO Job H3) j t1 t2 ->
forall Δ : instant,
is_true (t1 + Δ < t2) ->
is_true
  (@cumulative_another_hep_job_interference Job PState arr_seq sched (@fifo.FIFO Job H3) j t1 (t1 + Δ) <=
   \sum_(tsko <- ts)
      @request_bound_function.task_request_bound_function Task H H0 tsko (@job_arrival Job H3 j - t1 + 1) -
   @task_cost Task H tsk)

bound_on_hep_workload is not universe polymorphic
Arguments bound_on_hep_workload {Task H H0 Job H1 H2 H3 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model arr_seq H_valid_arrival_sequence H_valid_job_cost ts%seq_scope
  H_all_jobs_from_taskset H_is_arrival_curve H_valid_arrival_curve tsk H_tsk_in_ts 
  sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j H_job_of_task 
  H_j_in_arrivals H_job_cost_positive t1 t2 H_busy_window Δ H_in_busy
bound_on_hep_workload is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload
Declared in library prosa.analysis.facts.priority.fifo_ahep_bound, line 85, characters 8-29
@bound_on_hep_workload
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : curves.MaxArrivals Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobArrival Job)
         (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H1 H2 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @curves.taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
       @curves.valid_taskset_arrival_curve Task ts (@curves.max_arrivals Task H0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H3 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall j : Equality.sort Job,
       is_true (@job_of_task Job Task H1 tsk j) ->
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval Job H3 H2 PState arr_seq sched (@fifo.FIFO Job H3) j t1 t2 ->
       forall Δ : instant,
       is_true (t1 + Δ < t2) ->
       is_true
         (@cumulative_another_hep_job_interference Job PState arr_seq sched (@fifo.FIFO Job H3) j t1 (t1 + Δ) <=
          \sum_(tsko <- ts)
             @request_bound_function.task_request_bound_function Task H H0 tsko
               (@job_arrival Job H3 j - t1 + 1) -
          @task_cost Task H tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.FifoAhepBound.bound_on_hep_workload : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
            ∀ (ts : List Task),
              Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                      Prosa.Model.Task.Arrival.Curves.max_arrivals →
                    ∀ (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                          Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                            Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                              ∀ (j : Job),
                                Prosa.Model.Task.Concept.job_of_task tsk j = true →
                                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                    Prosa.Model.Job.Properties.job_cost_positive j = true →
                                      ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval arr_seq sched j
                                            t1 t2 →
                                          ∀ (Δ : Prosa.Behavior.Time.instant),
                                            t1 + Δ < t2 →
                                              Prosa.Analysis.Definitions.Interference.cumulative_another_hep_job_interference
                                                  arr_seq sched j t1 (t1 + Δ) ≤
                                                (Prosa.Util.Sum.sumSeq ts fun tsko =>
                                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                      tsko (Prosa.Behavior.Job.job_arrival j - t1 + 1)) -
                                                  Prosa.Model.Task.Concept.task_cost tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_FifoAhepBound_bound_on_hep_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_13),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_13 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_13,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_23 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_20 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq
         inst_9 ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9) ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_13 PState,
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_13
         inst_23 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_13 PState sched
         inst_20 ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_13 Task
            inst_3
            inst_16 tsk j)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_13 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_13
            inst_20 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval Job
         inst_13
         inst_23
         inst_20 PState arr_seq
         sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_13
            inst_23)
         j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_instant,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference Job
            inst_13 PState arr_seq
            sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_13
               inst_23)
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Util_Sum_sumSeq Task ts
               (fun tsko : Task =>
                Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_6
                  inst_9 tsko
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                        Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_13
                           inst_23
                           j)
                        t1)
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_6 tsk))
```
