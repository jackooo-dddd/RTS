# `arrivals_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_uniq`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq`
- Certificate: `arrivals_uniq_correspondence`

## Official Rocq

```coq
arrivals_uniq :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
@arrival_sequence_uniq Job arr_seq ->
forall t1 t2 : instant, is_true (@uniq Job (@arrivals_between Job arr_seq t1 t2))

arrivals_uniq is not universe polymorphic
Arguments arrivals_uniq {Job H} arr_seq H_consistent_arrival_times _ t1 t2
arrivals_uniq is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_uniq
Declared in library prosa.analysis.facts.behavior.arrivals, line 362, characters 10-23
@arrivals_uniq
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       @arrival_sequence_uniq Job arr_seq ->
       forall t1 t2 : instant, is_true (@uniq Job (@arrivals_between Job arr_seq t1 t2))
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
      ∀ (t1 t2 : Prosa.Behavior.Time.instant), (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_uniq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       List_Nodup Job
         (Prosa_Behavior_Arrival_sequence_arrivals_between Job
            inst_3 arr_seq t1 t2)
```
