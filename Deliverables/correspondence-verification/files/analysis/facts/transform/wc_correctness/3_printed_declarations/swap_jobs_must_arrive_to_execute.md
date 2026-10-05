# `swap_jobs_must_arrive_to_execute`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.swap_jobs_must_arrive_to_execute`
- Certificate: `swap_jobs_must_arrive_to_execute_correspondence`

## Official Rocq

```coq
swap_jobs_must_arrive_to_execute :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
@jobs_must_be_ready_to_execute Job H (processor_state Job) sched H0
  (@basic.basic_ready_instance Job (processor_state Job) H H0) ->
forall t1 : instant,
@jobs_must_arrive_to_execute Job H (processor_state Job)
  (@swapped Job (processor_state Job) sched t1 (@find_swap_candidate Job H H1 arr_seq sched t1))

swap_jobs_must_arrive_to_execute is not universe polymorphic
Arguments swap_jobs_must_arrive_to_execute {Job H H0 H1} arr_seq sched H_jobs_must_be_ready t1 j t _
swap_jobs_must_arrive_to_execute is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute
Declared in library prosa.analysis.facts.transform.wc_correctness, line 98, characters 10-42
@swap_jobs_must_arrive_to_execute
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
       @jobs_must_be_ready_to_execute Job H (processor_state Job) sched H0
         (@basic.basic_ready_instance Job (processor_state Job) H H0) ->
       forall t1 : instant,
       @jobs_must_arrive_to_execute Job H (processor_state Job)
         (@swapped Job (processor_state Job) sched t1 (@find_swap_candidate Job H H1 arr_seq sched t1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.swap_jobs_must_arrive_to_execute : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched →
    ∀ (t1 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute
        (Prosa.Analysis.Transform.Swap.swapped sched t1
          (Prosa.Analysis.Transform.WcTrans.find_swap_candidate arr_seq sched t1))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_swap_jobs_must_arrive_to_execute
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
                       inst_3)),
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
       forall t1 : Prosa_Behavior_Time_instant,
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_Swap_swapped_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched t1
            (Prosa_Analysis_Transform_WcTrans_find_swap_candidate Job
               inst_3
               inst_6
               inst_12 arr_seq
               sched t1))
```
