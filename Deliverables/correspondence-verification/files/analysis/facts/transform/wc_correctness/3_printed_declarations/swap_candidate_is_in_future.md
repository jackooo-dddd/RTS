# `swap_candidate_is_in_future`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.swap_candidate_is_in_future`
- Certificate: `swap_candidate_is_in_future_correspondence`

## Official Rocq

```coq
swap_candidate_is_in_future :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t1 : instant),
is_true (t1 <= @find_swap_candidate Job H H1 arr_seq sched t1)

swap_candidate_is_in_future is not universe polymorphic
Arguments swap_candidate_is_in_future {Job H H1} arr_seq sched t1
swap_candidate_is_in_future is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future
Declared in library prosa.analysis.facts.transform.wc_correctness, line 69, characters 10-37
@swap_candidate_is_in_future
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (t1 : instant),
       is_true (t1 <= @find_swap_candidate Job H H1 arr_seq sched t1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.swap_candidate_is_in_future : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t1 : Prosa.Behavior.Time.instant), t1 ≤ Prosa.Analysis.Transform.WcTrans.find_swap_candidate arr_seq sched t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_swap_candidate_is_in_future
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
         (t1 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
         (Prosa_Analysis_Transform_WcTrans_find_swap_candidate Job
            inst_3
            inst_6
            inst_9 arr_seq sched
            t1)
```
