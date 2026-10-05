# `mwa_service_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.mwa_service_bound`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_service_bound`
- Certificate: `mwa_service_bound_correspondence`

## Official Rocq

```coq
mwa_service_bound :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t : instant) (j : Equality.sort Job) 
  (t0 : instant),
is_true
  (@service Job (processor_state Job) sched j t0 <=
   @service Job (processor_state Job) (@make_wc_at Job H H1 arr_seq sched t) j t0)

mwa_service_bound is not universe polymorphic
Arguments mwa_service_bound {Job H H1} arr_seq sched t j t
mwa_service_bound is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.mwa_service_bound
Declared in library prosa.analysis.facts.transform.wc_correctness, line 158, characters 10-27
@mwa_service_bound
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (t : instant) (j : Equality.sort Job) 
         (t0 : instant),
       is_true
         (@service Job (processor_state Job) sched j t0 <=
          @service Job (processor_state Job) (@make_wc_at Job H H1 arr_seq sched t) j t0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_service_bound : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant) (j : Job) (t0 : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service sched j t0 ≤
    Prosa.Behavior.Service.service (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t) j t0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_service_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
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
         (t : Prosa_Behavior_Time_instant) (j : Job) (t0 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t0)
         (Prosa_Behavior_Service_service_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_WcTrans_make_wc_at Job
               inst_3
               inst_6
               inst_9 arr_seq sched t)
            j t0)
```
