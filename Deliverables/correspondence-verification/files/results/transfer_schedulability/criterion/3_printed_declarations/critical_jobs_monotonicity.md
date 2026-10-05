# `critical_jobs_monotonicity`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.critical_jobs_monotonicity`
- Certificate: `critical_jobs_monotonicity_correspondence`

## Official Rocq

```coq
critical_jobs_monotonicity :
forall {Job : JobType} (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) (t1 t2 t3 : nat),
is_true (t1 <= t2 <= t3) ->
forall j : Equality.sort Job,
is_true (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3) ->
is_true (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)

critical_jobs_monotonicity is not universe polymorphic
Arguments critical_jobs_monotonicity {Job} ref_sched online_sched ref_job_cost online_job_cost 
  arr_seq (t1 t2 t3)%nat_scope _ j _
critical_jobs_monotonicity is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity
Declared in library prosa.results.transfer_schedulability.criterion, line 384, characters 10-36
@critical_jobs_monotonicity
     : forall (Job : JobType) (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) 
         (t1 t2 t3 : nat),
       is_true (t1 <= t2 <= t3) ->
       forall j : Equality.sort Job,
       is_true (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3) ->
       is_true (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.critical_jobs_monotonicity : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (t1 t2 t3 : ℕ),
  (decide (t1 ≤ t2) && decide (t2 ≤ t3)) = true →
    ∀ (j : Job),
      decide
            (j ∈
              Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                online_job_cost arr_seq t2 t3) =
          true →
        decide
            (j ∈
              Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                online_job_cost arr_seq t1 t3) =
          true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_critical_jobs_monotonicity
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (ref_sched
          online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (ref_job_cost
          online_job_cost : Prosa_Behavior_Job_JobCost Job
                              inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (t1 t2 t3 : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t2) (Nat_decLe t1 t2))
            (Decidable_decide (LE_le_inst1 Nat instLENat t2 t3) (Nat_decLe t2 t3)))
         Bool_true ->
       forall j : Job,
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                  inst_3
                  ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j
               (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                  inst_3
                  ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3)))
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                  inst_3
                  ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j
               (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                  inst_3
                  ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)))
         Bool_true
```
