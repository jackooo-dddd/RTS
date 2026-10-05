# `interference_plus_sched_le_serv_of_task_plus_task_interference_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle`
- Certificate: `interference_plus_sched_le_serv_of_task_plus_task_interference_idle_correspondence`

## Official Rocq

```coq
interference_plus_sched_le_serv_of_task_plus_task_interference_idle :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall (tsk : Equality.sort Task) {H3 : Interference Job} (j : Equality.sort Job) (t1 t : instant),
is_true (@is_idle Job PState arr_seq sched t) ->
is_true
  (nat_of_bool (@interference Job H3 j t) + @service_at Job PState sched j t <=
   @service_of_jobs_at Job PState sched (@job_of_task Job Task H0 tsk)
     (@arrivals_between Job arr_seq t1 (t1 + (@job_arrival Job H1 j - t1) + 1)) t +
   nat_of_bool (@task_interference Job Task H0 PState arr_seq sched H3 j t))

interference_plus_sched_le_serv_of_task_plus_task_interference_idle is not universe polymorphic
Arguments interference_plus_sched_le_serv_of_task_plus_task_interference_idle {Task Job H0 H1 PState} 
  arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute 
  tsk {H3} j t1 t H_idle
interference_plus_sched_le_serv_of_task_plus_task_interference_idle is opaque
Expands to: Constant
            prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle
Declared in library prosa.analysis.abstract.IBF.task, line 302, characters 14-81
@interference_plus_sched_le_serv_of_task_plus_task_interference_idle
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (tsk : Equality.sort Task) (H3 : Interference Job) (j : Equality.sort Job) (t1 t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       is_true
         (nat_of_bool (@interference Job H3 j t) + @service_at Job PState sched j t <=
          @service_of_jobs_at Job PState sched (@job_of_task Job Task H0 tsk)
            (@arrivals_between Job arr_seq t1 (t1 + (@job_arrival Job H1 j - t1) + 1)) t +
          nat_of_bool (@task_interference Job Task H0 PState arr_seq sched H3 j t))
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (tsk : Task) [inst_4 : Prosa.Analysis.Abstract.Definitions.Interference Job] (j : Job)
            (t1 t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
              (Prosa.Analysis.Abstract.Definitions.interference j t).toNat +
                  Prosa.Behavior.Service.service_at sched j t ≤
                Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs_at sched (Prosa.Model.Task.Concept.job_of_task tsk)
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                      (t1 + (Prosa.Behavior.Job.job_arrival j - t1) + 1))
                    t +
                  (Prosa.Analysis.Abstract.IBF.Task.task_interference arr_seq sched j t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_interference_plus_sched_le_serv_of_task_plus_task_interference_idle
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
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
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
         (inst_40 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (j : Job) (t1 t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq sched t)
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Job_work Nat (instHAdd_inst1 Nat instAddNat)
            (Bool_toNat
               (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
                  inst_3
                  inst_40 j t))
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
                  inst_40 j t)))
```
