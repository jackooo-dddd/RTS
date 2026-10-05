# `abstractly_work_conserving`

- Kind (Rocq): Fact
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.abstractly_work_conserving`
- Certificate: `abstractly_work_conserving_correspondence`

## Official Rocq

```coq
abstractly_work_conserving :
forall {Job : JobType} {H3 : JobArrival Job} {H4 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H3 (ideal.processor_state Job) sched H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
@work_conserving.work_conserving Job H3 H4 (ideal.processor_state Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched ->
@work_conserving Job H3 H4 (ideal.processor_state Job) arr_seq sched
  (@ideal_jlfp_interference Job H3 arr_seq sched) (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched)

abstractly_work_conserving is not universe polymorphic
Arguments abstractly_work_conserving {Job H3 H4} arr_seq H_valid_arrival_sequence 
  sched H_valid_schedule H_work_conserving j t1 t2 t _ _ _ _
abstractly_work_conserving is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 170, characters 7-33
@abstractly_work_conserving
     : forall (Job : JobType) (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H3 (ideal.processor_state Job) sched H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
       @work_conserving.work_conserving Job H3 H4 (ideal.processor_state Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched ->
       @work_conserving Job H3 H4 (ideal.processor_state Job) arr_seq sched
         (@ideal_jlfp_interference Job H3 arr_seq sched)
         (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.abstractly_work_conserving : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
          Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_abstractly_work_conserving
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
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
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_10
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_13
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_10
            inst_13)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_10
            inst_13)
         arr_seq sched ->
       Prosa_Analysis_Abstract_Definitions_work_conserving_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_10))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_13 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_10))
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
```
