# `instantiated_task_intra_interference_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.instantiated_task_intra_interference_is_bounded`
- Certificate: `instantiated_task_intra_interference_is_bounded_correspondence`

## Official Rocq

```coq
instantiated_task_intra_interference_is_bounded :
forall {Task : TaskType} {Job : JobType} {Cost : JobCost Job} {H : JobArrival Job} 
  {H0 : JobTask Job Task} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {JobReady0 : @JobReady Job PState Cost H} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H PState sched Cost JobReady0 arr_seq ->
forall (tsk : Equality.sort Task) (service_inversion_bound : duration -> duration),
@service_inversion_is_bounded Job H Cost PState JobReady0 arr_seq sched JLFP
  (@rs_jlfp_interference Job Cost H PState JobReady0 JLFP arr_seq sched)
  (@rs_jlfp_interfering_workload Job Cost H PState JobReady0 JLFP arr_seq sched) service_inversion_bound ->
forall athep_workload_bound : duration -> duration -> duration,
@athep_workload_is_bounded Task Job Cost H H0 PState JLFP arr_seq sched tsk athep_workload_bound ->
forall readiness_interference_bound : duration -> duration -> duration,
@readiness_interference_is_bounded Job H Cost PState JobReady0 arr_seq sched JLFP
  (@rs_jlfp_interference Job Cost H PState JobReady0 JLFP arr_seq sched)
  (@rs_jlfp_interfering_workload Job Cost H PState JobReady0 JLFP arr_seq sched) readiness_interference_bound ->
@task_intra_interference_is_bounded_by Job Task H0 H Cost PState arr_seq sched tsk
  (@rs_jlfp_interference Job Cost H PState JobReady0 JLFP arr_seq sched)
  (@rs_jlfp_interfering_workload Job Cost H PState JobReady0 JLFP arr_seq sched)
  (task_intra_IBF service_inversion_bound athep_workload_bound readiness_interference_bound)

instantiated_task_intra_interference_is_bounded is not universe polymorphic
Arguments instantiated_task_intra_interference_is_bounded {Task Job Cost H H0 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  {JobReady0 JLFP} H_priority_is_reflexive arr_seq H_valid_arrival_sequence sched 
  H_valid_schedule tsk service_inversion_bound%function_scope H_service_inversion_is_bounded
  athep_workload_bound%function_scope H_workload_is_bounded readiness_interference_bound%function_scope
  H_readiness_interference_bounded t1 t2 Δ j _ _ _ _ _ X _
instantiated_task_intra_interference_is_bounded is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded
Declared in library prosa.analysis.abstract.restricted_supply.task_ibf_readiness, line 79, characters 8-55
@instantiated_task_intra_interference_is_bounded
     : forall (Task : TaskType) (Job : JobType) (Cost : JobCost Job) (H : JobArrival Job)
         (H0 : JobTask Job Task) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall (JobReady0 : @JobReady Job PState Cost H) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H PState sched Cost JobReady0 arr_seq ->
       forall (tsk : Equality.sort Task) (service_inversion_bound : duration -> duration),
       @service_inversion_is_bounded Job H Cost PState JobReady0 arr_seq sched JLFP
         (@rs_jlfp_interference Job Cost H PState JobReady0 JLFP arr_seq sched)
         (@rs_jlfp_interfering_workload Job Cost H PState JobReady0 JLFP arr_seq sched)
         service_inversion_bound ->
       forall athep_workload_bound : duration -> duration -> duration,
       @athep_workload_is_bounded Task Job Cost H H0 PState JLFP arr_seq sched tsk athep_workload_bound ->
       forall readiness_interference_bound : duration -> duration -> duration,
       @readiness_interference_is_bounded Job H Cost PState JobReady0 arr_seq sched JLFP
         (@rs_jlfp_interference Job Cost H PState JobReady0 JLFP arr_seq sched)
         (@rs_jlfp_interfering_workload Job Cost H PState JobReady0 JLFP arr_seq sched)
         readiness_interference_bound ->
       @task_intra_interference_is_bounded_by Job Task H0 H Cost PState arr_seq sched tsk
         (@rs_jlfp_interference Job Cost H PState JobReady0 JLFP arr_seq sched)
         (@rs_jlfp_interfering_workload Job Cost H PState JobReady0 JLFP arr_seq sched)
         (task_intra_IBF service_inversion_bound athep_workload_bound readiness_interference_bound)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.instantiated_task_intra_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [Cost : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState]
          [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    ∀ (tsk : Task)
                      (service_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                      Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion_is_bounded arr_seq
                          sched service_inversion_bound →
                        ∀
                          (athep_workload_bound :
                            Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                          Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded arr_seq sched tsk
                              athep_workload_bound →
                            ∀
                              (readiness_interference_bound :
                                Prosa.Behavior.Time.duration →
                                  Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                              Prosa.Analysis.Definitions.ReadinessInterference.readiness_interference_is_bounded arr_seq
                                  sched readiness_interference_bound →
                                Prosa.Analysis.Abstract.IBF.SupplyTask.task_intra_interference_is_bounded_by arr_seq
                                  sched tsk
                                  (Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.task_intra_IBF
                                    service_inversion_bound athep_workload_bound readiness_interference_bound)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_instantiated_task_intra_interference_is_bounded
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
         (JobReady0 : Prosa_Behavior_Ready_JobReady Job
                        inst_7
                        PState Cost
                        inst_12)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
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
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7
         inst_12
         PState sched Cost JobReady0 arr_seq ->
       forall (tsk : Task)
         (service_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion_is_bounded Job
         inst_7
         inst_12 Cost
         PState JobReady0 arr_seq sched JLFP
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
            inst_7
            inst_12
            Cost PState JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload Job
            inst_7
            inst_12
            Cost PState JobReady0 arr_seq sched JLFP)
         service_inversion_bound ->
       forall
         athep_workload_bound : Prosa_Behavior_Time_duration ->
                                Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded Task
         inst_3 Job
         inst_7 Cost
         inst_12
         inst_15
         PState JLFP arr_seq sched tsk athep_workload_bound ->
       forall
         readiness_interference_bound : Prosa_Behavior_Time_duration ->
                                        Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_ReadinessInterference_readiness_interference_is_bounded Job
         inst_7
         inst_12 Cost
         PState JobReady0 arr_seq sched JLFP
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
            inst_7
            inst_12
            Cost PState JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload Job
            inst_7
            inst_12
            Cost PState JobReady0 arr_seq sched JLFP)
         readiness_interference_bound ->
       Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_15
         inst_12 Cost
         PState arr_seq sched tsk
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
            inst_7
            inst_12
            Cost PState JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload Job
            inst_7
            inst_12
            Cost PState JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF service_inversion_bound
            athep_workload_bound readiness_interference_bound)
```
