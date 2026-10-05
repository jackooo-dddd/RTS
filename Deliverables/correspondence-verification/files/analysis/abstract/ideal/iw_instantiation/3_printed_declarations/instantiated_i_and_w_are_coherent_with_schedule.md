# `instantiated_i_and_w_are_coherent_with_schedule`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_i_and_w_are_coherent_with_schedule`
- Certificate: `instantiated_i_and_w_are_coherent_with_schedule_correspondence`

## Official Rocq

```coq
instantiated_i_and_w_are_coherent_with_schedule :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall {JobReady0 : @JobReady Job (ideal.processor_state Job) H2 H1},
@work_bearing_readiness Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched JLFP ->
@work_conserving.work_conserving Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched ->
@reflexive_job_priorities Job JLFP ->
@work_conserving Job H1 H2 (ideal.processor_state Job) arr_seq sched
  (@ideal_jlfp_interference Job arr_seq sched JLFP)
  (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP)

instantiated_i_and_w_are_coherent_with_schedule is not universe polymorphic
Arguments instantiated_i_and_w_are_coherent_with_schedule {Job H1 H2} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_priority_is_reflexive {JobReady0} H_work_bearing_readiness H_work_conserving 
  H_policy_reflexive j t1 t2 t _ _ _ _
instantiated_i_and_w_are_coherent_with_schedule is opaque
Expands to: Constant
            prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 597, characters 14-61
@instantiated_i_and_w_are_coherent_with_schedule
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall JobReady0 : @JobReady Job (ideal.processor_state Job) H2 H1,
       @work_bearing_readiness Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched JLFP ->
       @work_conserving.work_conserving Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched ->
       @reflexive_job_priorities Job JLFP ->
       @work_conserving Job H1 H2 (ideal.processor_state Job) arr_seq sched
         (@ideal_jlfp_interference Job arr_seq sched JLFP)
         (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_i_and_w_are_coherent_with_schedule : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
              Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                        Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_i_and_w_are_coherent_with_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_7
         inst_10
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_13 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall
         JobReady0 : Prosa_Behavior_Ready_JobReady_inst4 Job
                       inst_7
                       (Prosa_Model_Processor_Ideal_processor_state Job
                          inst_7)
                       inst_13
                       inst_10,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4 Job
         inst_7
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         JobReady0 arr_seq sched JLFP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         JobReady0 arr_seq sched ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       Prosa_Analysis_Abstract_Definitions_work_conserving_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            JLFP)
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_13 arr_seq sched
            JLFP)
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
```
