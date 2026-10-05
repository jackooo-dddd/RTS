# `instantiated_task_intra_interference_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound.instantiated_task_intra_interference_is_bounded`
- Certificate: `instantiated_task_intra_interference_is_bounded_correspondence`

## Official Rocq

```coq
instantiated_task_intra_interference_is_bounded :
forall {Task : TaskType} {Job : JobType} {Cost : JobCost Job} {H : JobArrival Job} 
  {H0 : JobTask Job Task} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@completed_jobs_dont_execute Job PState sched Cost ->
forall (tsk : Equality.sort Task) (service_inversion_bound : duration -> duration),
@service_inversion_is_bounded_by Task Job H0 H Cost PState arr_seq sched JLFP tsk service_inversion_bound ->
forall athep_workload_bound : duration -> duration -> duration,
@athep_workload_is_bounded Task Job Cost H H0 PState JLFP arr_seq sched tsk athep_workload_bound ->
@task_intra_interference_is_bounded_by Job Task H0 H Cost PState arr_seq sched tsk
  (@rs_jlfp_interference Job PState JLFP arr_seq sched)
  (@rs_jlfp_interfering_workload Job Cost PState JLFP arr_seq sched)
  (task_intra_IBF service_inversion_bound athep_workload_bound)

instantiated_task_intra_interference_is_bounded is not universe polymorphic
Arguments instantiated_task_intra_interference_is_bounded {Task Job Cost H H0 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  {JLFP} H_priority_is_reflexive arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk service_inversion_bound%function_scope
  H_service_inversion_is_bounded athep_workload_bound%function_scope H_workload_is_bounded 
  t1 t2 Δ j _ _ _ _ _ X _
instantiated_task_intra_interference_is_bounded is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded
Declared in
library prosa.analysis.abstract.restricted_supply.task_intra_interference_bound, line 98, characters 8-55
@instantiated_task_intra_interference_is_bounded
     : forall (Task : TaskType) (Job : JobType) (Cost : JobCost Job) (H : JobArrival Job)
         (H0 : JobTask Job Task) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @completed_jobs_dont_execute Job PState sched Cost ->
       forall (tsk : Equality.sort Task) (service_inversion_bound : duration -> duration),
       @service_inversion_is_bounded_by Task Job H0 H Cost PState arr_seq sched JLFP tsk
         service_inversion_bound ->
       forall athep_workload_bound : duration -> duration -> duration,
       @athep_workload_is_bounded Task Job Cost H H0 PState JLFP arr_seq sched tsk athep_workload_bound ->
       @task_intra_interference_is_bounded_by Job Task H0 H Cost PState arr_seq sched tsk
         (@rs_jlfp_interference Job PState JLFP arr_seq sched)
         (@rs_jlfp_interfering_workload Job Cost PState JLFP arr_seq sched)
         (task_intra_IBF service_inversion_bound athep_workload_bound)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound.instantiated_task_intra_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [Cost : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
                    Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                      Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                        ∀ (tsk : Task)
                          (service_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                          Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by arr_seq
                              sched tsk service_inversion_bound →
                            ∀
                              (athep_workload_bound :
                                Prosa.Behavior.Time.duration →
                                  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                              Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded arr_seq sched tsk
                                  athep_workload_bound →
                                Prosa.Analysis.Abstract.IBF.SupplyTask.task_intra_interference_is_bounded_by arr_seq
                                  sched tsk
                                  (Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound.task_intra_IBF
                                    service_inversion_bound athep_workload_bound)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_TaskIntraInterferenceBound_instantiated_task_intra_interference_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (Cost : Prosa_Behavior_Job_JobCost Job
                   inst_7)
         (inst_12 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_15 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7
            Task
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7
         PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7
         PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7
         PState ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7
         JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_12
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7
         PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_12
         PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7
         PState sched Cost ->
       forall (tsk : Task)
         (service_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by Task
         inst_3
         Job
         inst_7
         inst_15
         inst_12
         Cost PState arr_seq sched JLFP tsk service_inversion_bound ->
       forall
         athep_workload_bound : Prosa_Behavior_Time_duration ->
                                Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded Task
         inst_3
         Job
         inst_7
         Cost
         inst_12
         inst_15
         PState JLFP arr_seq sched tsk athep_workload_bound ->
       Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference_is_bounded_by Job
         inst_7
         Task
         inst_3
         inst_15
         inst_12
         Cost PState arr_seq sched tsk
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_7
            PState arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_7
            Cost PState arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_TaskIntraInterferenceBound_task_intra_IBF
            service_inversion_bound athep_workload_bound)
```
