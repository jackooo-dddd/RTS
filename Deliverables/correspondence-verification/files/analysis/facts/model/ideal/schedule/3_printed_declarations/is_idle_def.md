# `is_idle_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.is_idle_def`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.is_idle_def`
- Certificate: `is_idle_def_correspondence`

## Official Rocq

```coq
is_idle_def :
forall {Job : JobType} (arr_seq : arrival_sequence Job) {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@valid_arrival_sequence Job H1 arr_seq ->
forall t : instant,
@is_idle Job (ideal.processor_state Job) arr_seq sched t = @ideal.ideal_is_idle Job sched t

is_idle_def is not universe polymorphic
Arguments is_idle_def {Job} arr_seq {H1} sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_arrival_times_are_valid t
is_idle_def is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.is_idle_def
Declared in library prosa.analysis.facts.model.ideal.schedule, line 216, characters 10-21
@is_idle_def
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @valid_arrival_sequence Job H1 arr_seq ->
       forall t : instant,
       @is_idle Job (ideal.processor_state Job) arr_seq sched t = @ideal.ideal_is_idle Job sched t
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.is_idle_def : ∀ (Job : Prosa.Behavior.Job.JobType) [inst : DecidableEq Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (t : Prosa.Behavior.Time.instant),
          Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = Prosa.Model.Processor.Ideal.ideal_is_idle sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_is_idle_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (inst_8 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_8
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_8 arr_seq ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            arr_seq sched t)
         (Prosa_Model_Processor_Ideal_ideal_is_idle Job
            inst_3 sched t)
```
