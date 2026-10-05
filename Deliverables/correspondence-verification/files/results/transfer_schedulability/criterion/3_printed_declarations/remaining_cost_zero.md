# `remaining_cost_zero`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.remaining_cost_zero`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.remaining_cost_zero`
- Certificate: `remaining_cost_zero_correspondence`

## Official Rocq

```coq
remaining_cost_zero :
forall {Job : JobType} (online_sched : @schedule Job (ideal.processor_state Job))
  (online_job_cost : JobCost Job),
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
forall (js : seq (Equality.sort Job)) (t : instant),
is_true (\sum_(j <- js) @remaining_cost_bound Job online_sched job_cost_bound j t == 0) ->
forall j : Equality.sort Job,
is_true (j \in js) ->
is_true (@completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t)

remaining_cost_zero is not universe polymorphic
Arguments remaining_cost_zero {Job} online_sched online_job_cost H_jobs_exec_on job_cost_bound
  H_job_cost_bounded%function_scope js%seq_scope t _ j _
remaining_cost_zero is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.remaining_cost_zero
Declared in library prosa.results.transfer_schedulability.criterion, line 332, characters 10-29
@remaining_cost_zero
     : forall (Job : JobType) (online_sched : @schedule Job (ideal.processor_state Job))
         (online_job_cost : JobCost Job),
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       forall (js : seq (Equality.sort Job)) (t : instant),
       is_true (\sum_(j <- js) @remaining_cost_bound Job online_sched job_cost_bound j t == 0) ->
       forall j : Equality.sort Job,
       is_true (j \in js) ->
       is_true (@completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.remaining_cost_zero : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (online_job_cost : Prosa.Behavior.Job.JobCost Job),
  Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
    ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
      (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
        ∀ (js : List Job) (t : Prosa.Behavior.Time.instant),
          decide
                ((Prosa.Util.Sum.sumSeq js fun j =>
                    Prosa.Results.TransferSchedulability.Criterion.remaining_cost_bound online_sched job_cost_bound j
                      t) =
                  0) =
              true →
            ∀ (j : Job), decide (j ∈ js) = true → Prosa.Behavior.Service.completed_by online_sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_remaining_cost_zero
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
       forall (js : List Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (@eq Nat
               (Prosa_Util_Sum_sumSeq Job js
                  (fun j : Job =>
                   Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
                     inst_3
                     online_sched job_cost_bound j t))
               (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
            (instDecidableEqNat
               (Prosa_Util_Sum_sumSeq Job js
                  (fun j : Job =>
                   Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job
                     inst_3
                     online_sched job_cost_bound j t))
               (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))))
         Bool_true ->
       forall j : Job,
       @eq Bool
         (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) js j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j js))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            online_sched online_job_cost j t)
         Bool_true
```
