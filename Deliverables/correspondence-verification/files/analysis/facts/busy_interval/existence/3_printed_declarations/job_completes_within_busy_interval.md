# `job_completes_within_busy_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.job_completes_within_busy_interval`
- Certificate: `job_completes_within_busy_interval_correspondence`

## Official Rocq

```coq
job_completes_within_busy_interval :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState) {JLFP : JLFP_policy Job}
  (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
@reflexive_job_priorities Job JLFP ->
forall t1 t2 : instant,
(fun t3 : instant => [eta @busy_interval Job Arrival Cost PState arr_seq sched JLFP j t3]) t1 t2 ->
is_true (@completed_by Job PState sched Cost j t2)

job_completes_within_busy_interval is not universe polymorphic
Arguments job_completes_within_busy_interval {Job Arrival Cost} arr_seq {PState} 
  sched {JLFP} j H_from_arrival_sequence H_priority_is_reflexive t1 t2 H_busy_interval
job_completes_within_busy_interval is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval
Declared in library prosa.analysis.facts.busy_interval.existence, line 74, characters 10-44
@job_completes_within_busy_interval
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (JLFP : JLFP_policy Job) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       @reflexive_job_priorities Job JLFP ->
       forall t1 t2 : instant,
       @busy_interval Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
       is_true (@completed_by Job PState sched Cost j t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.job_completes_within_busy_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job),
  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
    Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
      ∀ (t1 t2 : Prosa.Behavior.Time.instant),
        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval arr_seq sched j t1 t2 →
          Prosa.Behavior.Service.completed_by sched j t2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_job_completes_within_busy_interval
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched
         JLFP j t1 t2 ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_9 j t2)
         Bool_true
```
