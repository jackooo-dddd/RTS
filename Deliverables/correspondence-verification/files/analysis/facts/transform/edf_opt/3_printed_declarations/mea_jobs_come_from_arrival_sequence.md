# `mea_jobs_come_from_arrival_sequence`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.mea_jobs_come_from_arrival_sequence`
- Certificate: `mea_jobs_come_from_arrival_sequence_correspondence`

## Official Rocq

```coq
mea_jobs_come_from_arrival_sequence :
forall {Job : JobType} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)) (t_edf : instant) (arr_seq : arrival_sequence Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) arr_seq

mea_jobs_come_from_arrival_sequence is not universe polymorphic
Arguments mea_jobs_come_from_arrival_sequence {Job H0 H1} sched t_edf arr_seq H_from_arr_seq j t _
mea_jobs_come_from_arrival_sequence is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence
Declared in library prosa.analysis.facts.transform.edf_opt, line 466, characters 10-45
@mea_jobs_come_from_arrival_sequence
     : forall (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)) (t_edf : instant)
         (arr_seq : arrival_sequence Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf)
         arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.mea_jobs_come_from_arrival_sequence : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobDeadline Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t_edf : Prosa.Behavior.Time.instant) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence (Prosa.Analysis.Transform.EdfTrans.make_edf_at sched t_edf)
      arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_mea_jobs_come_from_arrival_sequence
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
         (t_edf : Prosa_Behavior_Time_instant)
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
         (Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
            inst_3
            inst_6
            inst_9 sched t_edf)
         arr_seq
```
