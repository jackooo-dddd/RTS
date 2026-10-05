# `arrivals_between_geq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_between_geq`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_geq`
- Certificate: `arrivals_between_geq_correspondence`

## Official Rocq

```coq
arrivals_between_geq :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (t1 t2 : nat),
is_true (t2 <= t1) -> @arrivals_between Job arr_seq t1 t2 = [::]

arrivals_between_geq is not universe polymorphic
Arguments arrivals_between_geq {Job} arr_seq (t1 t2)%nat_scope _
arrivals_between_geq is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_between_geq
Declared in library prosa.analysis.facts.behavior.arrivals, line 371, characters 10-30
@arrivals_between_geq
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (t1 t2 : nat),
       is_true (t2 <= t1) -> @arrivals_between Job arr_seq t1 t2 = [::]
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_between_geq : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (t1 t2 : ℕ),
  t2 ≤ t1 → Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2 = []
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_geq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t2 t1 ->
       @eq (List Job)
         (Prosa_Behavior_Arrival_sequence_arrivals_between Job
            inst_3 arr_seq t1 t2)
         (List_nil Job)
```
