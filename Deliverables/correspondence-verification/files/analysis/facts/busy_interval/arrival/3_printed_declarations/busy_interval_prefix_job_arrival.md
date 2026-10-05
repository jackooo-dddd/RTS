# `busy_interval_prefix_job_arrival`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Arrival.busy_interval_prefix_job_arrival`
- Certificate: `busy_interval_prefix_job_arrival_correspondence`

## Official Rocq

```coq
busy_interval_prefix_job_arrival :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JLFP_policy Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
  (j : Equality.sort Job) (t t' : instant),
@busy_interval_prefix Job H H0 PState arr_seq sched H1 j t t' -> is_true (t <= @job_arrival Job H j)

busy_interval_prefix_job_arrival is not universe polymorphic
Arguments busy_interval_prefix_job_arrival {Job H H0 H1 PState} sched arr_seq j t t' _
busy_interval_prefix_job_arrival is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival
Declared in library prosa.analysis.facts.busy_interval.arrival, line 23, characters 7-39
@busy_interval_prefix_job_arrival
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JLFP_policy Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
         (j : Equality.sort Job) (t t' : instant),
       @busy_interval_prefix Job H H0 PState arr_seq sched H1 j t t' -> is_true (t <= @job_arrival Job H j)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Arrival.busy_interval_prefix_job_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (j : Job) (t t' : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t t' →
    t ≤ Prosa.Behavior.Job.job_arrival j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Arrival_busy_interval_prefix_job_arrival
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (j : Job) (t t' : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched
         inst_12 j t t' ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
```
