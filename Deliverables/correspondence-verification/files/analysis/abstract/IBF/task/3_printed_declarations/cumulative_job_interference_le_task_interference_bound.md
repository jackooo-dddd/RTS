# `cumulative_job_interference_le_task_interference_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.cumulative_job_interference_le_task_interference_bound`
- Certificate: `cumulative_job_interference_le_task_interference_bound_correspondence`

## Official Rocq

```coq
cumulative_job_interference_le_task_interference_bound :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {jc : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched jc ->
forall (tsk : Equality.sort Task) {H3 : Interference Job} {H4 : InterferingWorkload Job},
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
   @task_workload_between Task Job H0 jc arr_seq tsk t1 (t1 + (@job_arrival Job H1 j - t1) + 1) -
   @job_cost Job jc j + @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x))

cumulative_job_interference_le_task_interference_bound is not universe polymorphic
Arguments cumulative_job_interference_le_task_interference_bound {Task Job H0 H1 jc PState}
  H_uniprocessor_proc_model H_unit_service_proc_model arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  tsk {H3 H4} H_work_conserving H_sequential_tasks
  H_interference_and_workload_consistent_with_sequential_tasks j H_j_arrives H_job_of_tsk 
  H_job_cost_positive t1 t2 H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
cumulative_job_interference_le_task_interference_bound is opaque
Expands to: Constant prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound
Declared in library prosa.analysis.abstract.IBF.task, line 530, characters 10-64
@cumulative_job_interference_le_task_interference_bound
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (jc : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched jc ->
       forall (tsk : Equality.sort Task) (H3 : Interference Job) (H4 : InterferingWorkload Job),
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
          @task_workload_between Task Job H0 jc arr_seq tsk t1 (t1 + (@job_arrival Job H1 j - t1) + 1) -
          @job_cost Job jc j + @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x))
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.cumulative_job_interference_le_task_interference_bound : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                  ∀ (tsk : Task) [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                    [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
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
                                            Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1 (t1 + x) ≤
                                              Prosa.Model.Aggregate.Workload.task_workload_between arr_seq tsk t1
                                                    (t1 + (Prosa.Behavior.Job.job_arrival j - t1) + 1) -
                                                  Prosa.Behavior.Job.job_cost j +
                                                Prosa.Analysis.Abstract.IBF.Task.cumul_task_interference arr_seq sched j
                                                  t1 (t1 + x)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_cumulative_job_interference_le_task_interference_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_17 : 
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
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_14 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_17 ->
       forall (tsk : Task)
         (inst_56 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_59 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_3
         inst_56
         inst_59
         inst_14
         inst_17 PState arr_seq sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_10
         inst_14
         inst_17 PState arr_seq sched ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_10
         inst_14
         inst_17 PState arr_seq sched tsk
         inst_56
         inst_59 ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_56
         inst_59
         inst_14
         inst_17 PState sched j t1 t2 ->
       forall x : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)
         t2 ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_17 j
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
            inst_3
            inst_56 j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Job_work Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Model_Aggregate_Workload_task_workload_between Task
                  inst_7 Job
                  inst_3
                  inst_10
                  inst_17 arr_seq tsk t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                        Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        t1
                        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                           Prosa_Behavior_Time_instant
                           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                           (Prosa_Behavior_Job_JobArrival_job_arrival Job
                              inst_3
                              inst_14 j)
                           t1))
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
               (Prosa_Behavior_Job_JobCost_job_cost Job
                  inst_3
                  inst_17 j))
            (Prosa_Analysis_Abstract_IBF_Task_cumul_task_interference Job
               inst_3 Task
               inst_7
               inst_10 PState arr_seq sched
               inst_56 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
```
