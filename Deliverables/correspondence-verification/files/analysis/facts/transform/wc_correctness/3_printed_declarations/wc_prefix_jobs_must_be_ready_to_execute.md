# `wc_prefix_jobs_must_be_ready_to_execute`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_must_be_ready_to_execute`
- Certificate: `wc_prefix_jobs_must_be_ready_to_execute_correspondence`

## Official Rocq

```coq
wc_prefix_jobs_must_be_ready_to_execute :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
  (h : instant),
@jobs_must_be_ready_to_execute Job H (processor_state Job) sched H0
  (@basic.basic_ready_instance Job (processor_state Job) H H0) ->
@jobs_must_be_ready_to_execute Job H (processor_state Job) (@wc_transform_prefix Job H H1 arr_seq sched h) H0
  (@basic.basic_ready_instance Job (processor_state Job) H H0)

wc_prefix_jobs_must_be_ready_to_execute is not universe polymorphic
Arguments wc_prefix_jobs_must_be_ready_to_execute {Job H H0 H1} arr_seq sched h _ j t _
wc_prefix_jobs_must_be_ready_to_execute is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute
Declared in library prosa.analysis.facts.transform.wc_correctness, line 550, characters 10-49
@wc_prefix_jobs_must_be_ready_to_execute
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
         (h : instant),
       @jobs_must_be_ready_to_execute Job H (processor_state Job) sched H0
         (@basic.basic_ready_instance Job (processor_state Job) H H0) ->
       @jobs_must_be_ready_to_execute Job H (processor_state Job)
         (@wc_transform_prefix Job H H1 arr_seq sched h) H0
         (@basic.basic_ready_instance Job (processor_state Job) H H0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.wc_prefix_jobs_must_be_ready_to_execute : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] [inst_3 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (h : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched →
    Prosa.Behavior.Ready.jobs_must_be_ready_to_execute
      (Prosa.Analysis.Transform.WcTrans.wc_transform_prefix arr_seq sched h)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_jobs_must_be_ready_to_execute
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
         (h : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_6
            inst_9) ->
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job
            inst_3
            inst_6
            inst_12 arr_seq sched
            h)
         inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_6
            inst_9)
```
