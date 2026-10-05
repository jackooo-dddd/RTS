# `arrives_after_beginning_of_busy_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.arrives_after_beginning_of_busy_interval`
- Certificate: `arrives_after_beginning_of_busy_interval_correspondence`

## Official Rocq

```coq
arrives_after_beginning_of_busy_interval :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {jc : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched jc ->
forall (tsk : Equality.sort Task) {H3 : Interference Job} {H4 : InterferingWorkload Job},
@interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 jc PState arr_seq sched tsk H3 H4 ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
is_true (@job_of_task Job Task H0 tsk j1) ->
is_true (@job_of_task Job Task H0 tsk j2) ->
is_true (@job_cost_positive Job jc j1) ->
forall t1 t2 : instant,
@busy_interval Job H1 jc PState sched H3 H4 j1 t1 t2 ->
forall t : nat,
is_true (t1 <= t) ->
is_true (@pending Job PState sched jc H1 j2 t) -> is_true (@arrived_between Job H1 j2 t1 t.+1)

arrives_after_beginning_of_busy_interval is not universe polymorphic
Arguments arrives_after_beginning_of_busy_interval {Task Job H0 H1 jc PState} H_unit_service_proc_model
  arr_seq H_valid_arrival_sequence sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  tsk {H3 H4} H_interference_and_workload_consistent_with_sequential_tasks j1 j2 
  H_j1_arrives H_j2_arrives H_j1_from_tsk H_j2_from_tsk H_j1_cost_positive t1 t2 
  H_busy_interval t%nat_scope _ _
arrives_after_beginning_of_busy_interval is opaque
Expands to: Constant prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval
Declared in library prosa.analysis.abstract.IBF.task, line 226, characters 10-50
@arrives_after_beginning_of_busy_interval
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (jc : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched jc ->
       forall (tsk : Equality.sort Task) (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 jc PState arr_seq sched tsk
         H3 H4 ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       is_true (@job_of_task Job Task H0 tsk j1) ->
       is_true (@job_of_task Job Task H0 tsk j2) ->
       is_true (@job_cost_positive Job jc j1) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 jc PState sched H3 H4 j1 t1 t2 ->
       forall t : nat,
       is_true (t1 <= t) ->
       is_true (@pending Job PState sched jc H1 j2 t) -> is_true (@arrived_between Job H1 j2 t1 t.+1)
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.arrives_after_beginning_of_busy_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
            Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
              ∀ (tsk : Task) [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks arr_seq
                    sched tsk →
                  ∀ (j1 j2 : Job),
                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
                        Prosa.Model.Task.Concept.job_of_task tsk j1 = true →
                          Prosa.Model.Task.Concept.job_of_task tsk j2 = true →
                            Prosa.Model.Job.Properties.job_cost_positive j1 = true →
                              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                Prosa.Analysis.Abstract.Definitions.busy_interval sched j1 t1 t2 →
                                  ∀ (t : ℕ),
                                    t1 ≤ t →
                                      Prosa.Behavior.Service.pending sched j2 t = true →
                                        Prosa.Behavior.Arrival_sequence.arrived_between j2 t1 (t + 1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_arrives_after_beginning_of_busy_interval
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
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_14 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_17 ->
       forall (tsk : Task)
         (inst_49 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_52 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3),
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_10
         inst_14
         inst_17 PState arr_seq sched tsk
         inst_49
         inst_52 ->
       forall j1 j2 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j1 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j2 ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j1)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j2)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_17 j1)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_49
         inst_52
         inst_14
         inst_17 PState sched j1 t1 t2 ->
       forall t : Nat,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_17
            inst_14 j2 t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_between Job
            inst_3
            inst_14 j2 t1
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         Bool_true
```
