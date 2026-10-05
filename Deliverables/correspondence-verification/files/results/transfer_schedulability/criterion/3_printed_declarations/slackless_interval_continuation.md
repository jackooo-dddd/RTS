# `slackless_interval_continuation`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.slackless_interval_continuation`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.slackless_interval_continuation`
- Certificate: `slackless_interval_continuation_correspondence`

## Official Rocq

```coq
slackless_interval_continuation :
forall {Job : JobType} {H : JobArrival Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
@transfer_schedulability_criterion Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
  job_cost_bound ->
forall t1 t2 : nat,
is_true
  (@slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2) ->
is_true
  (@contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2) ->
is_true
  [forall delta,
     @slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
       (t1 + @nat_of_ord (t2 - t1) delta) t2]

slackless_interval_continuation is not universe polymorphic
Arguments slackless_interval_continuation {Job H} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq H_valid_arrivals H_jobs_exec_on job_cost_bound H_job_cost_bounded%function_scope
  H_ts_criterion (t1 t2)%nat_scope _ _
slackless_interval_continuation is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.slackless_interval_continuation
Declared in library prosa.results.transfer_schedulability.criterion, line 951, characters 10-41
@slackless_interval_continuation
     : forall (Job : JobType) (H : JobArrival Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       @transfer_schedulability_criterion Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
         job_cost_bound ->
       forall t1 t2 : nat,
       is_true
         (@slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            t1 t2) ->
       is_true
         (@contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1
            t2) ->
       is_true
         [forall delta,
            @slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
              job_cost_bound (t1 + @nat_of_ord (t2 - t1) delta) t2]
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.slackless_interval_continuation : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
      ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
        (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
          Prosa.Results.TransferSchedulability.Criterion.transfer_schedulability_criterion ref_sched online_sched
              ref_job_cost online_job_cost arr_seq job_cost_bound →
            ∀ (t1 t2 : ℕ),
              Prosa.Results.TransferSchedulability.Criterion.slackless_interval ref_sched online_sched ref_job_cost
                    online_job_cost arr_seq job_cost_bound t1 t2 =
                  true →
                Prosa.Results.TransferSchedulability.Criterion.contiguously_nps ref_sched online_sched ref_job_cost
                      online_job_cost arr_seq job_cost_bound t1 t2 =
                    true →
                  ((List.range' 0 (t2 - t1)).all fun delta =>
                      Prosa.Results.TransferSchedulability.Criterion.slackless_interval ref_sched online_sched
                        ref_job_cost online_job_cost arr_seq job_cost_bound (t1 + delta) t2) =
                    true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_slackless_interval_continuation
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (ref_sched
          online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (ref_job_cost
          online_job_cost : Prosa_Behavior_Job_JobCost Job
                              inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
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
       Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion Job
         inst_3 ref_sched
         online_sched ref_job_cost online_job_cost arr_seq job_cost_bound ->
       forall t1 t2 : Nat,
       @eq Bool
         (Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job
            inst_3 ref_sched
            online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2)
         Bool_true ->
       @eq Bool
         (Prosa_Results_TransferSchedulability_Criterion_contiguously_nps Job
            inst_3 ref_sched
            online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2)
         Bool_true ->
       @eq Bool
         (List_all_inst1 Nat
            (List_range' (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
               (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1)
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (fun delta : Nat =>
             Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t1 delta) t2))
         Bool_true
```
