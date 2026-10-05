# `job_arrival_between_P`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.job_arrival_between_P`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_P`
- Certificate: `job_arrival_between_P_correspondence`

## Official Rocq

```coq
job_arrival_between_P :
forall {Job : JobType} {H : JobArrival Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (j : Equality.sort Job) (P : Equality.sort Job -> bool) (t1 t2 : instant),
is_true (j \in @arrivals_between_P Job arr_seq P t1 t2) -> is_true (t1 <= @job_arrival Job H j < t2)

job_arrival_between_P is not universe polymorphic
Arguments job_arrival_between_P {Job H} arr_seq H_consistent_arrival_times j P%function_scope t1 t2 _
job_arrival_between_P is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.job_arrival_between_P
Declared in library prosa.analysis.facts.behavior.arrivals, line 336, characters 10-31
@job_arrival_between_P
     : forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (j : Equality.sort Job) (P : Equality.sort Job -> bool) (t1 t2 : instant),
       is_true (j \in @arrivals_between_P Job arr_seq P t1 t2) -> is_true (t1 <= @job_arrival Job H j < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.job_arrival_between_P : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (P : Job → Bool) (t1 t2 : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t2) = true →
        (decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) && decide (Prosa.Behavior.Job.job_arrival j < t2)) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_between_P
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
       forall (j : Job) (P : Job -> Bool) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
                  inst_3 arr_seq P t1 t2)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
                  inst_3 arr_seq P t1 t2)))
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j))
               (Nat_decLe t1
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)
                  t2)
               (Nat_decLt
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)
                  t2)))
         Bool_true
```
