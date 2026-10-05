# `remaining_cost_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.remaining_cost_invariant`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.remaining_cost_invariant`
- Certificate: `remaining_cost_invariant_correspondence`

## Official Rocq

```coq
remaining_cost_invariant :
forall {Job : JobType} (online_sched : @schedule Job (ideal.processor_state Job))
  (online_job_cost : JobCost Job),
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
forall (js : seq (Equality.sort Job)) (t1 t2 : nat),
is_true (t1 <= t2) ->
is_true (@uniq Job js) ->
(forall t : nat,
 is_true (t1 <= t < t2) ->
 exists j : Equality.sort Job,
   is_true ((j \in js) && @scheduled_at Job (ideal.processor_state Job) online_sched j t)) ->
\sum_(j <- js) @remaining_cost_bound Job online_sched job_cost_bound j t1 =
\sum_(j <- js) @remaining_cost_bound Job online_sched job_cost_bound j t2 + (t2 - t1)

remaining_cost_invariant is not universe polymorphic
Arguments remaining_cost_invariant {Job} online_sched online_job_cost H_jobs_exec_on 
  job_cost_bound H_job_cost_bounded%function_scope js%seq_scope (t1 t2)%nat_scope 
  _ _ _%function_scope
remaining_cost_invariant is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.remaining_cost_invariant
Declared in library prosa.results.transfer_schedulability.criterion, line 273, characters 10-34
@remaining_cost_invariant
     : forall (Job : JobType) (online_sched : @schedule Job (ideal.processor_state Job))
         (online_job_cost : JobCost Job),
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       forall (js : seq (Equality.sort Job)) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       is_true (@uniq Job js) ->
       (forall t : nat,
        is_true (t1 <= t < t2) ->
        exists j : Equality.sort Job,
          is_true ((j \in js) && @scheduled_at Job (ideal.processor_state Job) online_sched j t)) ->
       \sum_(j <- js) @remaining_cost_bound Job online_sched job_cost_bound j t1 =
       \sum_(j <- js) @remaining_cost_bound Job online_sched job_cost_bound j t2 + (t2 - t1)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.remaining_cost_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (online_job_cost : Prosa.Behavior.Job.JobCost Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
    ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
      (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
        ∀ (js : List Job) (t1 t2 : ℕ),
          t1 ≤ t2 →
            js.Nodup →
              (∀ (t : ℕ),
                  (decide (t1 ≤ t) && decide (t < t2)) = true →
                    ∃ j, (decide (j ∈ js) && Prosa.Behavior.Service.scheduled_at online_sched j t) = true) →
                (Prosa.Util.Sum.sumSeq js fun j =>
                    Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j
                      t1) =
                  (Prosa.Util.Sum.sumSeq js fun j =>
                      Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j
                        t2) +
                    (t2 - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_remaining_cost_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (online_job_cost : Prosa_Behavior_Job_JobCost Job
                              inst_3),
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         online_sched online_job_cost ->
       forall
         job_cost_bound : Prosa_Behavior_Job_JobCost Job
                            inst_3,
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             online_job_cost j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)) ->
       forall (js : List Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       List_Nodup Job js ->
       (forall t : Nat,
        @eq Bool
          (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
          Bool_true ->
        Exists Job
          (fun j : Job =>
           Bool_and
             (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) js j)
                (List_instDecidableMemOfLawfulBEq Job
                   (instBEqOfDecidableEq Job
                      inst_3)
                   (instLawfulBEq Job
                      inst_3)
                   j js))
             (Prosa_Behavior_Service_scheduled_at_inst4 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)
                online_sched j t) =
           Bool_true)) ->
       @eq Nat
         (Prosa_Util_Sum_sumSeq Job js
            (fun j : Job =>
             Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
               inst_3
               online_sched job_cost_bound j t1))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Util_Sum_sumSeq Job js
               (fun j : Job =>
                Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
                  inst_3
                  online_sched job_cost_bound j t2))
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1))
```
