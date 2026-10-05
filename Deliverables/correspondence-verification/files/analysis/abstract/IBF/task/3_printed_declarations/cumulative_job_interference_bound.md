# `cumulative_job_interference_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.cumulative_job_interference_bound`
- Certificate: `cumulative_job_interference_bound_correspondence`

## Official Rocq

```coq
cumulative_job_interference_bound :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {jc : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched jc ->
@arrivals_have_valid_job_costs Task H Job H0 jc arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {H2 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H0 arr_seq H2 ts ->
forall {H3 : Interference Job} {H4 : InterferingWorkload Job},
@work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
@sequential_tasks Job Task H0 H1 jc PState arr_seq sched ->
@interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 jc PState arr_seq sched tsk H3 H4 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (@job_cost_positive Job jc j) ->
forall t1 t2 : instant,
@busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
forall x : duration,
is_true (t1 + x < t2) ->
is_true (~~ @completed_by Job PState sched jc j (t1 + x)) ->
is_true
  (@cumulative_interference Job H3 j t1 (t1 + x) <=
   @task_request_bound_function Task H H2 tsk (@job_arrival Job H1 j - t1 + 1) - @task_cost Task H tsk +
   @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x))

cumulative_job_interference_bound is not universe polymorphic
Arguments cumulative_job_interference_bound {Task H Job H0 H1 jc PState} H_uniprocessor_proc_model
  H_unit_service_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost ts%seq_scope 
  tsk H_tsk_in_ts {H2} H_is_arrival_curve {H3 H4} H_work_conserving H_sequential_tasks
  H_interference_and_workload_consistent_with_sequential_tasks j H_j_arrives H_job_of_tsk 
  H_job_cost_positive t1 t2 H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
cumulative_job_interference_bound is opaque
Expands to: Constant prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound
Declared in library prosa.analysis.abstract.IBF.task, line 546, characters 10-43
@cumulative_job_interference_bound
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched jc ->
       @arrivals_have_valid_job_costs Task H Job H0 jc arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall H2 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H0 arr_seq H2 ts ->
       forall (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
       @sequential_tasks Job Task H0 H1 jc PState arr_seq sched ->
       @interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 jc PState arr_seq sched tsk
         H3 H4 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (@job_cost_positive Job jc j) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
       forall x : duration,
       is_true (t1 + x < t2) ->
       is_true (~~ @completed_by Job PState sched jc j (t1 + x)) ->
       is_true
         (@cumulative_interference Job H3 j t1 (t1 + x) <=
          @task_request_bound_function Task H H2 tsk (@job_arrival Job H1 j - t1 + 1) - @task_cost Task H tsk +
          @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x))
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.cumulative_job_interference_bound : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                    ∀ (ts : List Task) (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        ∀ [inst_6 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                            ∀ [inst_7 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                              [inst_8 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                              Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                  Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks
                                      arr_seq sched tsk →
                                    ∀ (j : Job),
                                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                        Prosa.Model.Task.Concept.job_of_task tsk j = true →
                                          Prosa.Model.Job.Properties.job_cost_positive j = true →
                                            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                              Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                                                ∀ (x : Prosa.Behavior.Time.duration),
                                                  t1 + x < t2 →
                                                    (!Prosa.Behavior.Service.completed_by sched j (t1 + x)) = true →
                                                      Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1
                                                          (t1 + x) ≤
                                                        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                              tsk (Prosa.Behavior.Job.job_arrival j - t1 + 1) -
                                                            Prosa.Model.Task.Concept.task_cost tsk +
                                                          Prosa.Analysis.Abstract.IBF.Task.cumul_task_interference
                                                            arr_seq sched j t1 (t1 + x)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_cumulative_job_interference_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_17 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_17 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_20 ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_7
         inst_10 Job
         inst_3
         inst_13
         inst_20 arr_seq ->
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_7)
               (instLawfulBEq Task inst_7) tsk
               ts))
         Bool_true ->
       forall
         inst_80 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_7,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_7 Job
         inst_3
         inst_13 arr_seq
         inst_80 ts ->
       forall
         (inst_89 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_92 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_3
         inst_89
         inst_92
         inst_17
         inst_20 PState arr_seq sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_13
         inst_17
         inst_20 PState arr_seq sched ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_13
         inst_17
         inst_20 PState arr_seq sched tsk
         inst_89
         inst_92 ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_13 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_20 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_89
         inst_92
         inst_17
         inst_20 PState sched j t1 t2 ->
       forall x : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)
         t2 ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_20 j
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
            inst_3
            inst_89 j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_7
                  inst_10
                  inst_80 tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                        Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_17 j)
                        t1)
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_7
                  inst_10 tsk))
            (Prosa_Analysis_Abstract_IBF_Task_cumul_task_interference Job
               inst_3 Task
               inst_7
               inst_13 PState arr_seq sched
               inst_89 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
```
