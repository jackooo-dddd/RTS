# `uniq_valid_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.uniq_valid_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.uniq_valid_arrival`
- Certificate: `uniq_valid_arrival_correspondence`

## Official Rocq

```coq
uniq_valid_arrival :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq -> @arrival_sequence_uniq Job arr_seq

uniq_valid_arrival is not universe polymorphic
Arguments uniq_valid_arrival {Job H} arr_seq _ t
uniq_valid_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.uniq_valid_arrival
Declared in library prosa.analysis.facts.behavior.arrivals, line 38, characters 8-26
@uniq_valid_arrival
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq -> @arrival_sequence_uniq Job arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.uniq_valid_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_uniq_valid_arrival
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
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq
```
