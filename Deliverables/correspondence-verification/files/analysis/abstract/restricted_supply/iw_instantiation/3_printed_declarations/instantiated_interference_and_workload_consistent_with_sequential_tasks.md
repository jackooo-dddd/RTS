# `instantiated_interference_and_workload_consistent_with_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks`
- Certificate: `instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence`

## Official Rocq

```coq
instantiated_interference_and_workload_consistent_with_sequential_tasks :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall tsk : Equality.sort Task,
@policy_respects_sequential_tasks Task Job H0 H1 JLFP ->
@interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 H2 PState arr_seq sched tsk
  (@rs_jlfp_interference Job PState arr_seq sched JLFP)
  (@rs_jlfp_interfering_workload Job H2 PState arr_seq sched JLFP)

instantiated_interference_and_workload_consistent_with_sequential_tasks is not universe polymorphic
Arguments instantiated_interference_and_workload_consistent_with_sequential_tasks 
  {Task Job H0 H1 H2 PState} H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model
  arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute {JLFP} H_priority_is_reflexive tsk H_policy_respects_sequential_tasks 
  j t1 t2 _ _ _ _
instantiated_interference_and_workload_consistent_with_sequential_tasks is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 516, characters 10-81
@instantiated_interference_and_workload_consistent_with_sequential_tasks
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall tsk : Equality.sort Task,
       @policy_respects_sequential_tasks Task Job H0 H1 JLFP ->
       @interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 H2 PState arr_seq sched tsk
         (@rs_jlfp_interference Job PState arr_seq sched JLFP)
         (@rs_jlfp_interfering_workload Job H2 PState arr_seq sched JLFP)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
            ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
              Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
                Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                    ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
                      Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                        ∀ (tsk : Task),
                          Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks JLFP →
                            Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks
                              arr_seq sched tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_instantiated_interference_and_workload_consistent_with_sequential_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7
            Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14
         PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState
         sched inst_17 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall tsk : Task,
       Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
         inst_3 Job
         inst_7
         inst_10
         inst_14 JLFP ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_10
         inst_14
         inst_17
         PState arr_seq sched tsk
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_7
            PState arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_7
            inst_17
            PState arr_seq sched JLFP)
```
