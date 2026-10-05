# `serv_of_task_le_workload_of_task_plus`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.serv_of_task_le_workload_of_task_plus`
- Certificate: `serv_of_task_le_workload_of_task_plus_correspondence`

## Official Rocq

```coq
serv_of_task_le_workload_of_task_plus :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {jc : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@completed_jobs_dont_execute Job PState sched jc ->
forall (tsk : Equality.sort Task) {H3 : Interference Job} {H4 : InterferingWorkload Job}
  (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
forall t1 t2 : instant,
@busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
forall x : duration,
is_true
  (@task_service_of_jobs_in Task Job H0 PState sched tsk
     (@arrivals_between Job arr_seq t1 (t1 + (@job_arrival Job H1 j - t1) + 1)) t1 
     (t1 + x) -
   @service_during Job PState sched j t1 (t1 + x) +
   @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x) <=
   @task_workload_between Task Job H0 jc arr_seq tsk t1 (t1 + (@job_arrival Job H1 j - t1) + 1) -
   @job_cost Job jc j + @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x))

serv_of_task_le_workload_of_task_plus is not universe polymorphic
Arguments serv_of_task_le_workload_of_task_plus {Task Job H0 H1 jc PState} H_unit_service_proc_model 
  arr_seq H_valid_arrival_sequence sched H_completed_jobs_dont_execute tsk {H3 H4} 
  j H_j_arrives H_job_of_tsk t1 t2 H_busy_interval x
serv_of_task_le_workload_of_task_plus is opaque
Expands to: Constant prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus
Declared in library prosa.analysis.abstract.IBF.task, line 509, characters 10-47
@serv_of_task_le_workload_of_task_plus
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (jc : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @completed_jobs_dont_execute Job PState sched jc ->
       forall (tsk : Equality.sort Task) (H3 : Interference Job) (H4 : InterferingWorkload Job)
         (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
       forall x : duration,
       is_true
         (@task_service_of_jobs_in Task Job H0 PState sched tsk
            (@arrivals_between Job arr_seq t1 (t1 + (@job_arrival Job H1 j - t1) + 1)) t1 
            (t1 + x) -
          @service_during Job PState sched j t1 (t1 + x) +
          @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x) <=
          @task_workload_between Task Job H0 jc arr_seq tsk t1 (t1 + (@job_arrival Job H1 j - t1) + 1) -
          @job_cost Job jc j + @cumul_task_interference Job Task H0 PState arr_seq sched H3 j t1 (t1 + x))
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.serv_of_task_le_workload_of_task_plus : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ (tsk : Task) [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
              [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] (j : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                Prosa.Model.Task.Concept.job_of_task tsk j = true →
                  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                    Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                      ∀ (x : Prosa.Behavior.Time.duration),
                        Prosa.Model.Aggregate.ServiceOfJobs.task_service_of_jobs_in sched tsk
                                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                                  (t1 + (Prosa.Behavior.Job.job_arrival j - t1) + 1))
                                t1 (t1 + x) -
                              Prosa.Behavior.Service.service_during sched j t1 (t1 + x) +
                            Prosa.Analysis.Abstract.IBF.Task.cumul_task_interference arr_seq sched j t1 (t1 + x) ≤
                          Prosa.Model.Aggregate.Workload.task_workload_between arr_seq tsk t1
                                (t1 + (Prosa.Behavior.Job.job_arrival j - t1) + 1) -
                              Prosa.Behavior.Job.job_cost j +
                            Prosa.Analysis.Abstract.IBF.Task.cumul_task_interference arr_seq sched j t1 (t1 + x)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_serv_of_task_le_workload_of_task_plus
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
          Prosa_Behavior_Job_JobCost Job inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
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
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_17 ->
       forall (tsk : Task)
         (inst_46 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_49 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_46
         inst_49
         inst_14
         inst_17 PState sched j t1 t2 ->
       forall x : Prosa_Behavior_Time_duration,
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Job_work Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in Task
                  inst_7 Job
                  inst_3
                  inst_10 PState sched tsk
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_3 arr_seq t1
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                        Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                           Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                              Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_3
                                 inst_14 j)
                              t1))
                        (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
                  t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))
               (Prosa_Behavior_Service_service_during Job
                  inst_3 PState sched j t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
            (Prosa_Analysis_Abstract_IBF_Task_cumul_task_interference Job
               inst_3 Task
               inst_7
               inst_10 PState arr_seq sched
               inst_46 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
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
               inst_46 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)))
```
