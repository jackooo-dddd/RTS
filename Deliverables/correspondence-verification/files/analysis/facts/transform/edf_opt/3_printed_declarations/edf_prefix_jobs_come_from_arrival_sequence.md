# `edf_prefix_jobs_come_from_arrival_sequence`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_jobs_come_from_arrival_sequence`
- Certificate: `edf_prefix_jobs_come_from_arrival_sequence_correspondence`

## Official Rocq

```coq
edf_prefix_jobs_come_from_arrival_sequence :
forall {Job : JobType} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)) (horizon : instant) (arr_seq : arrival_sequence Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job)
  (@edf_transform_prefix Job H0 H1 sched horizon) arr_seq

edf_prefix_jobs_come_from_arrival_sequence is not universe polymorphic
Arguments edf_prefix_jobs_come_from_arrival_sequence {Job H0 H1} sched horizon arr_seq H_from_arr_seq j t _
edf_prefix_jobs_come_from_arrival_sequence is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence
Declared in library prosa.analysis.facts.transform.edf_opt, line 620, characters 10-52
@edf_prefix_jobs_come_from_arrival_sequence
     : forall (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)) (horizon : instant)
         (arr_seq : arrival_sequence Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job)
         (@edf_transform_prefix Job H0 H1 sched horizon) arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_jobs_come_from_arrival_sequence : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobDeadline Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (horizon : Prosa.Behavior.Time.instant) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence
      (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched horizon) arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_jobs_come_from_arrival_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (horizon : Prosa_Behavior_Time_instant)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
            inst_3
            inst_6
            inst_9 sched horizon)
         arr_seq
```
