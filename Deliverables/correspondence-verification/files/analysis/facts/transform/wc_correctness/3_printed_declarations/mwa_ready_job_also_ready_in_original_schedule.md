# `mwa_ready_job_also_ready_in_original_schedule`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_ready_job_also_ready_in_original_schedule`
- Certificate: `mwa_ready_job_also_ready_in_original_schedule_correspondence`

## Official Rocq

```coq
mwa_ready_job_also_ready_in_original_schedule :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
  (t : instant) (j : Equality.sort Job) (t0 : instant),
is_true
  (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
     (@make_wc_at Job H H1 arr_seq sched t) j t0) ->
is_true
  (@job_ready Job (processor_state Job) H0 H (@basic.basic_ready_instance Job (processor_state Job) H H0)
     sched j t0)

mwa_ready_job_also_ready_in_original_schedule is not universe polymorphic
Arguments mwa_ready_job_also_ready_in_original_schedule {Job H H0 H1} arr_seq sched t j t _
mwa_ready_job_also_ready_in_original_schedule is opaque
Expands to: Constant
            prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule
Declared in library prosa.analysis.facts.transform.wc_correctness, line 183, characters 10-55
@mwa_ready_job_also_ready_in_original_schedule
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
         (t : instant) (j : Equality.sort Job) (t0 : instant),
       is_true
         (@job_ready Job (processor_state Job) H0 H
            (@basic.basic_ready_instance Job (processor_state Job) H H0)
            (@make_wc_at Job H H1 arr_seq sched t) j t0) ->
       is_true
         (@job_ready Job (processor_state Job) H0 H
            (@basic.basic_ready_instance Job (processor_state Job) H H0) sched j t0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_ready_job_also_ready_in_original_schedule : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] [inst_3 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant) (j : Job) (t0 : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Ready.job_ready (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t) j t0 = true →
    Prosa.Behavior.Ready.job_ready sched j t0 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_ready_job_also_ready_in_original_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant) (j : Job) (t0 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_9
            inst_6
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_6
               inst_9)
            (Prosa_Analysis_Transform_WcTrans_make_wc_at Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched t)
            j t0)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_9
            inst_6
            (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               inst_6
               inst_9)
            sched j t0)
         Bool_true
```
