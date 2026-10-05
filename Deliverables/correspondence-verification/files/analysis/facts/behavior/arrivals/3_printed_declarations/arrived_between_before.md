# `arrived_between_before`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrived_between_before`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_before`
- Certificate: `arrived_between_before_correspondence`

## Official Rocq

```coq
arrived_between_before :
forall {Job : JobType} {H : JobArrival Job} (j : Equality.sort Job) (t1 t2 : instant),
is_true (@arrived_between Job H j t1 t2) -> is_true (@arrived_before Job H j t2)

arrived_between_before is not universe polymorphic
Arguments arrived_between_before {Job H} j t1 t2 _
arrived_between_before is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrived_between_before
Declared in library prosa.analysis.facts.behavior.arrivals, line 15, characters 8-30
@arrived_between_before
     : forall (Job : JobType) (H : JobArrival Job) (j : Equality.sort Job) (t1 t2 : instant),
       is_true (@arrived_between Job H j t1 t2) -> is_true (@arrived_before Job H j t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Arrival_sequence.arrived_between j t1 t2 = true →
    Prosa.Behavior.Arrival_sequence.arrived_before j t2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrived_between_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_between Job
            inst_3
            inst_6 j t1 t2)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_before Job
            inst_3
            inst_6 j t2)
         Bool_true
```
