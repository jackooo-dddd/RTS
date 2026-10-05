# `consistent_times_valid_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.consistent_times_valid_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.consistent_times_valid_arrival`
- Certificate: `consistent_times_valid_arrival_correspondence`

## Official Rocq

```coq
consistent_times_valid_arrival :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq -> @consistent_arrival_times Job H arr_seq

consistent_times_valid_arrival is not universe polymorphic
Arguments consistent_times_valid_arrival {Job H} arr_seq _ j t _
consistent_times_valid_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.consistent_times_valid_arrival
Declared in library prosa.analysis.facts.behavior.arrivals, line 31, characters 8-38
@consistent_times_valid_arrival
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq -> @consistent_arrival_times Job H arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.consistent_times_valid_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_consistent_times_valid_arrival
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq
```
