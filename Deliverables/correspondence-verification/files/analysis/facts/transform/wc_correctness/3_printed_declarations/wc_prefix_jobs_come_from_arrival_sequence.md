# `wc_prefix_jobs_come_from_arrival_sequence`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_come_from_arrival_sequence`
- Certificate: `wc_prefix_jobs_come_from_arrival_sequence_correspondence`

## Official Rocq

```coq
wc_prefix_jobs_come_from_arrival_sequence :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (h : instant),
@jobs_come_from_arrival_sequence Job (processor_state Job) sched arr_seq ->
@jobs_come_from_arrival_sequence Job (processor_state Job) (@wc_transform_prefix Job H H1 arr_seq sched h)
  arr_seq

wc_prefix_jobs_come_from_arrival_sequence is not universe polymorphic
Arguments wc_prefix_jobs_come_from_arrival_sequence {Job H H1} arr_seq sched h _ j t _
wc_prefix_jobs_come_from_arrival_sequence is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence
Declared in library prosa.analysis.facts.transform.wc_correctness, line 537, characters 10-51
@wc_prefix_jobs_come_from_arrival_sequence
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (h : instant),
       @jobs_come_from_arrival_sequence Job (processor_state Job) sched arr_seq ->
       @jobs_come_from_arrival_sequence Job (processor_state Job)
         (@wc_transform_prefix Job H H1 arr_seq sched h) arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_come_from_arrival_sequence : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (h : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence
      (Prosa.Analysis.Transform.WcTrans.wc_transform_prefix arr_seq sched h) arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_jobs_come_from_arrival_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (h : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job
            inst_3
            inst_6
            inst_9 arr_seq sched h)
         arr_seq
```
