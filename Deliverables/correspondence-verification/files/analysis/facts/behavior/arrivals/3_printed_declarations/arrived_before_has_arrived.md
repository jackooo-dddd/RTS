# `arrived_before_has_arrived`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrived_before_has_arrived`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrived_before_has_arrived`
- Certificate: `arrived_before_has_arrived_correspondence`

## Official Rocq

```coq
arrived_before_has_arrived :
forall {Job : JobType} {H : JobArrival Job} (j : Equality.sort Job) (t : instant),
is_true (@arrived_before Job H j t) -> is_true (@has_arrived Job H j t)

arrived_before_has_arrived is not universe polymorphic
Arguments arrived_before_has_arrived {Job H} j t _
arrived_before_has_arrived is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrived_before_has_arrived
Declared in library prosa.analysis.facts.behavior.arrivals, line 23, characters 8-34
@arrived_before_has_arrived
     : forall (Job : JobType) (H : JobArrival Job) (j : Equality.sort Job) (t : instant),
       is_true (@arrived_before Job H j t) -> is_true (@has_arrived Job H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrived_before_has_arrived : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Arrival_sequence.arrived_before j t = true → Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrived_before_has_arrived
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_before Job
            inst_3
            inst_6 j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_3
            inst_6 j t)
         Bool_true
```
