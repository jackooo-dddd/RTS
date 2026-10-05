# `index_lte_implies_arrival_lte_P`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.index_lte_implies_arrival_lte_P`
- Lean: `Prosa.Analysis.Facts.JobIndex.index_lte_implies_arrival_lte_P`
- Certificate: `index_lte_implies_arrival_lte_P_correspondence`

## Official Rocq

```coq
index_lte_implies_arrival_lte_P :
forall {Job : JobType} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall (j1 j2 : Equality.sort Job) (P : Equality.sort Job -> bool) (t1 t2 : instant),
is_true (j1 \in @arrivals_between_P Job arr_seq P t1 t2) ->
is_true (j2 \in @arrivals_between_P Job arr_seq P t1 t2) ->
is_true
  (@index Job j1 (@arrivals_between_P Job arr_seq P t1 t2) <=
   @index Job j2 (@arrivals_between_P Job arr_seq P t1 t2)) ->
is_true (@job_arrival Job H0 j1 <= @job_arrival Job H0 j2)

index_lte_implies_arrival_lte_P is not universe polymorphic
Arguments index_lte_implies_arrival_lte_P {Job H0} arr_seq H_valid_arrival_sequence 
  j1 j2 P%function_scope t1 t2 _ _ _
index_lte_implies_arrival_lte_P is opaque
Expands to: Constant prosa.analysis.facts.job_index.index_lte_implies_arrival_lte_P
Declared in library prosa.analysis.facts.job_index, line 139, characters 8-39
@index_lte_implies_arrival_lte_P
     : forall (Job : JobType) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall (j1 j2 : Equality.sort Job) (P : Equality.sort Job -> bool) (t1 t2 : instant),
       is_true (j1 \in @arrivals_between_P Job arr_seq P t1 t2) ->
       is_true (j2 \in @arrivals_between_P Job arr_seq P t1 t2) ->
       is_true
         (@index Job j1 (@arrivals_between_P Job arr_seq P t1 t2) <=
          @index Job j2 (@arrivals_between_P Job arr_seq P t1 t2)) ->
       is_true (@job_arrival Job H0 j1 <= @job_arrival Job H0 j2)
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.index_lte_implies_arrival_lte_P : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j1 j2 : Job) (P : Job → Bool) (t1 t2 : Prosa.Behavior.Time.instant),
      decide (j1 ∈ Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t2) = true →
        decide (j2 ∈ Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t2) = true →
          List.idxOf j1 (Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t2) ≤
              List.idxOf j2 (Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t2) →
            Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_index_lte_implies_arrival_lte_P
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall (j1 j2 : Job) (P : Job -> Bool) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
                  inst_3 arr_seq P t1 t2)
               j1)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job inst_3)
               (instLawfulBEq Job inst_3) j1
               (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
                  inst_3 arr_seq P t1 t2)))
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
                  inst_3 arr_seq P t1 t2)
               j2)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job inst_3)
               (instLawfulBEq Job inst_3) j2
               (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
                  inst_3 arr_seq P t1 t2)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (List_idxOf Job
            (instBEqOfDecidableEq Job inst_3) j1
            (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
               inst_3 arr_seq P t1 t2))
         (List_idxOf Job
            (instBEqOfDecidableEq Job inst_3) j2
            (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
               inst_3 arr_seq P t1 t2)) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j1)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j2)
```
