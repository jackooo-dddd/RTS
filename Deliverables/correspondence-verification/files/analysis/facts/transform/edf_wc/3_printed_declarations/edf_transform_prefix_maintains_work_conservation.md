# `edf_transform_prefix_maintains_work_conservation`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation`
- Lean: `Prosa.Analysis.Facts.Transform.EdfWc.edf_transform_prefix_maintains_work_conservation`
- Certificate: `edf_transform_prefix_maintains_work_conservation_correspondence`

## Official Rocq

```coq
edf_transform_prefix_maintains_work_conservation :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
  (horizon : instant),
(fun sched0 : @schedule Job (processor_state Job) =>
 @scheduled_behavior_premises Job H H0 H1 arr_seq sched0 /\
 @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
   arr_seq sched0)
  sched ->
(fun sched0 : @schedule Job (processor_state Job) =>
 @scheduled_behavior_premises Job H H0 H1 arr_seq sched0 /\
 @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
   arr_seq sched0)
  (@edf_transform_prefix Job H0 H1 sched horizon)

edf_transform_prefix_maintains_work_conservation is not universe polymorphic
Arguments edf_transform_prefix_maintains_work_conservation {Job H H0 H1} arr_seq sched horizon _
edf_transform_prefix_maintains_work_conservation is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation
Declared in library prosa.analysis.facts.transform.edf_wc, line 334, characters 8-56
@edf_transform_prefix_maintains_work_conservation
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
         (horizon : instant),
       @scheduled_behavior_premises Job H H0 H1 arr_seq sched /\
       @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
         arr_seq sched ->
       @scheduled_behavior_premises Job H H0 H1 arr_seq (@edf_transform_prefix Job H0 H1 sched horizon) /\
       @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
         arr_seq (@edf_transform_prefix Job H0 H1 sched horizon)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfWc.edf_transform_prefix_maintains_work_conservation : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (horizon : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises arr_seq sched ∧
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
    Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises arr_seq
        (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched horizon) ∧
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq
        (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched horizon)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfWc_edf_transform_prefix_maintains_work_conservation
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (horizon : Prosa_Behavior_Time_instant),
       And
         (Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises Job
            inst_3
            inst_6
            inst_9
            inst_12 arr_seq sched)
         (Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
            inst_3
            inst_12
            inst_6
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_12
               inst_6)
            arr_seq sched) ->
       And
         (Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises Job
            inst_3
            inst_6
            inst_9
            inst_12 arr_seq
            (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
               inst_3
               inst_9
               inst_12 sched horizon))
         (Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
            inst_3
            inst_12
            inst_6
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_12
               inst_6)
            arr_seq
            (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
               inst_3
               inst_9
               inst_12 sched horizon))
```
