# `interference_plus_sched_le_serv_of_task_plus_task_interference_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_job`
- Certificate: `interference_plus_sched_le_serv_of_task_plus_task_interference_job_correspondence`

## Official Rocq

```coq
interference_plus_sched_le_serv_of_task_plus_task_interference_job :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {jc : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall (tsk : Equality.sort Task) {H3 : Interference Job} {H4 : InterferingWorkload Job},
@work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (@job_cost_positive Job jc j) ->
forall t1 t2 : instant,
@busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
forall x : duration,
is_true (t1 + x < t2) ->
forall t : instant,
is_true (t1 <= t < t1 + x) ->
forall j' : Equality.sort Job,
is_true (@scheduled_at Job PState sched j' t) ->
is_true (@job_of_task Job Task H0 tsk j') ->
@service_at Job PState sched j' t = 0 ->
is_true
  (nat_of_bool (@interference Job H3 j t) + @service_at Job PState sched j t <=
   @service_of_jobs_at Job PState sched (@job_of_task Job Task H0 tsk)
     (@arrivals_between Job arr_seq t1 (t1 + (@job_arrival Job H1 j - t1) + 1)) t +
   nat_of_bool (@task_interference Job Task H0 PState arr_seq sched H3 j t))

interference_plus_sched_le_serv_of_task_plus_task_interference_job is not universe polymorphic
Arguments interference_plus_sched_le_serv_of_task_plus_task_interference_job {Task Job H0 H1 jc PState}
  H_uniprocessor_proc_model H_unit_service_proc_model arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk {H3 H4} 
  H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval 
  x H_inside_busy_interval t H_t_in_interval j' H_sched H_not_job_of_tsk H_serv
interference_plus_sched_le_serv_of_task_plus_task_interference_job is opaque
Expands to: Constant
            prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job
Declared in library prosa.analysis.abstract.IBF.task, line 372, characters 14-80
@interference_plus_sched_le_serv_of_task_plus_task_interference_job
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (jc : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (tsk : Equality.sort Task) (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (@job_cost_positive Job jc j) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 jc PState sched H3 H4 j t1 t2 ->
       forall x : duration,
       is_true (t1 + x < t2) ->
       forall t : instant,
       is_true (t1 <= t < t1 + x) ->
       forall j' : Equality.sort Job,
       is_true (@scheduled_at Job PState sched j' t) ->
       is_true (@job_of_task Job Task H0 tsk j') ->
       @service_at Job PState sched j' t = 0 ->
       is_true
         (nat_of_bool (@interference Job H3 j t) + @service_at Job PState sched j t <=
          @service_of_jobs_at Job PState sched (@job_of_task Job Task H0 tsk)
            (@arrivals_between Job arr_seq t1 (t1 + (@job_arrival Job H1 j - t1) + 1)) t +
          nat_of_bool (@task_interference Job Task H0 PState arr_seq sched H3 j t))
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_job : ∀
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
                ∀ (tsk : Task) [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                  [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                  Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                    ∀ (j : Job),
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                        Prosa.Model.Task.Concept.job_of_task tsk j = true →
                          Prosa.Model.Job.Properties.job_cost_positive j = true →
                            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                              Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                                ∀ (x : Prosa.Behavior.Time.duration),
                                  t1 + x < t2 →
                                    ∀ (t : Prosa.Behavior.Time.instant),
                                      (decide (t1 ≤ t) && decide (t < t1 + x)) = true →
                                        ∀ (j' : Job),
                                          Prosa.Behavior.Service.scheduled_at sched j' t = true →
                                            Prosa.Model.Task.Concept.job_of_task tsk j' = true →
                                              Prosa.Behavior.Service.service_at sched j' t = 0 →
                                                (Prosa.Analysis.Abstract.Definitions.interference j t).toNat +
                                                    Prosa.Behavior.Service.service_at sched j t ≤
                                                  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at sched
                                                      (Prosa.Model.Task.Concept.job_of_task tsk)
                                                      (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                                                        (t1 + (Prosa.Behavior.Job.job_arrival j - t1) + 1))
                                                      t +
                                                    (Prosa.Analysis.Abstract.IBF.Task.task_interference arr_seq sched j
                                                        t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_interference_plus_sched_le_serv_of_task_plus_task_interference_job
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
       forall (tsk : Task)
         (inst_53 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_56 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_3
         inst_53
         inst_56
         inst_14
         inst_17 PState arr_seq sched ->
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
         inst_53
         inst_56
         inst_14
         inst_17 PState sched j t1 t2 ->
       forall x : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x)
         t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))
               (Nat_decLt t
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 x))))
         Bool_true ->
       forall j' : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j')
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j' t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Job_work Nat (instHAdd_inst1 Nat instAddNat)
            (Bool_toNat
               (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
                  inst_3
                  inst_53 j t))
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job
               inst_3 PState sched
               (Prosa_Model_Task_Concept_job_of_task Job
                  inst_3 Task
                  inst_7
                  inst_10 tsk)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1
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
               t)
            (Bool_toNat
               (Prosa_Analysis_Abstract_IBF_Task_task_interference Job
                  inst_3 Task
                  inst_7
                  inst_10 PState arr_seq sched
                  inst_53 j t)))
```
