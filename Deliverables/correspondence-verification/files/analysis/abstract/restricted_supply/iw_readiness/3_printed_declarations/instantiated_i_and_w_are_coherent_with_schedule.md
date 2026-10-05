# `instantiated_i_and_w_are_coherent_with_schedule`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_are_coherent_with_schedule`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_i_and_w_are_coherent_with_schedule`
- Certificate: `instantiated_i_and_w_are_coherent_with_schedule_correspondence`

## Official Rocq

```coq
instantiated_i_and_w_are_coherent_with_schedule :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {JobReady0 : @JobReady Job PState H2 H1} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
@definitions.work_conserving Job H1 H2 PState arr_seq sched
  (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
  (@rs_readiness_jlfp_interfering_workload Job H1 H2 PState JobReady0 arr_seq sched JLFP)

instantiated_i_and_w_are_coherent_with_schedule is not universe polymorphic
Arguments instantiated_i_and_w_are_coherent_with_schedule {Job H1 H2 PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model {JobReady0} arr_seq H_valid_arrival_sequence sched 
  H_valid_schedule {JLFP} H_priority_is_reflexive H_work_conserving j t1 t2 t _ _ 
  _ _
instantiated_i_and_w_are_coherent_with_schedule is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_are_coherent_with_schedule
Declared in library prosa.analysis.abstract.restricted_supply.iw_readiness, line 570, characters 14-61
@instantiated_i_and_w_are_coherent_with_schedule
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall (JobReady0 : @JobReady Job PState H2 H1) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       @definitions.work_conserving Job H1 H2 PState arr_seq sched
         (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
         (@rs_readiness_jlfp_interfering_workload Job H1 H2 PState JobReady0 arr_seq sched JLFP)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_i_and_w_are_coherent_with_schedule : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState]
        (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
                Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                  Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                    Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_instantiated_i_and_w_are_coherent_with_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         (JobReady0 : Prosa_Behavior_Ready_JobReady Job
                        inst_7
                        PState
                        inst_13
                        inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7
         inst_10 PState
         sched inst_13
         JobReady0 arr_seq ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_7
         inst_10
         inst_13 PState
         JobReady0 arr_seq sched ->
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
            inst_7
            inst_10
            inst_13 PState
            JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload Job
            inst_7
            inst_10
            inst_13 PState
            JobReady0 arr_seq sched JLFP)
         inst_10
         inst_13 PState
         arr_seq sched
```
