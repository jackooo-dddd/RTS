# `abstract_busy_interval_arrivals_before`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_arrivals_before`
- Certificate: `abstract_busy_interval_arrivals_before_correspondence`

## Official Rocq

```coq
abstract_busy_interval_arrivals_before :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
forall t1 t2 : instant,
@busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
@consistent_arrival_times Job H1 arr_seq -> is_true (j \in @arrivals_before Job arr_seq t2)

abstract_busy_interval_arrivals_before is not universe polymorphic
Arguments abstract_busy_interval_arrivals_before {Job H1 H2 PState H3 H4} arr_seq 
  sched j H_from_arrival_sequence t1 t2 H_busy_interval H_consistent_arrival_times
abstract_busy_interval_arrivals_before is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before
Declared in library prosa.analysis.abstract.busy_interval, line 158, characters 7-45
@abstract_busy_interval_arrivals_before
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       forall t1 t2 : instant,
       @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
       @consistent_arrival_times Job H1 arr_seq -> is_true (j \in @arrivals_before Job arr_seq t2)
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_arrivals_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (j : Job),
  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
        Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
          decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_abstract_busy_interval_arrivals_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_14 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_17 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_14
         inst_17
         inst_6
         inst_9 PState sched j t1 t2 ->
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_before Job
                  inst_3 arr_seq t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_before Job
                  inst_3 arr_seq t2)))
         Bool_true
```
