# `delay_if_no_critical_job_is_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.delay_if_no_critical_job_is_scheduled`
- Certificate: `delay_if_no_critical_job_is_scheduled_correspondence`

## Official Rocq

```coq
delay_if_no_critical_job_is_scheduled :
forall {Job : JobType} {H : JobArrival Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
forall t1 t2 : nat,
is_true
  (@slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq online_job_cost t1 t2) ->
{in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2,
  forall j : Equality.sort Job, is_true (~~ @scheduled_at Job (ideal.processor_state Job) online_sched j t1)} ->
exists j : Equality.sort Job,
  is_true (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) /\
  is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t2)

delay_if_no_critical_job_is_scheduled is not universe polymorphic
Arguments delay_if_no_critical_job_is_scheduled {Job H} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq H_valid_arrivals H_jobs_exec_on (t1 t2)%nat_scope _ _
delay_if_no_critical_job_is_scheduled is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled
Declared in library prosa.results.transfer_schedulability.criterion, line 1146, characters 8-45
@delay_if_no_critical_job_is_scheduled
     : forall (Job : JobType) (H : JobArrival Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) online_sched online_job_cost ->
       forall t1 t2 : nat,
       is_true
         (@slackless_interval Job ref_sched online_sched ref_job_cost online_job_cost arr_seq online_job_cost
            t1 t2) ->
       {in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2,
         forall j : Equality.sort Job,
         is_true (~~ @scheduled_at Job (ideal.processor_state Job) online_sched j t1)} ->
       exists j : Equality.sort Job,
         is_true (j \in @critical_jobs Job ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) /\
         is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t2)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.delay_if_no_critical_job_is_scheduled : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Ready.completed_jobs_dont_execute online_sched →
      ∀ (t1 t2 : ℕ),
        Prosa.Results.TransferSchedulability.Criterion.slackless_interval ref_sched online_sched ref_job_cost
              online_job_cost arr_seq online_job_cost t1 t2 =
            true →
          (∀ (j : Job),
              decide
                    (j ∈
                      Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                        online_job_cost arr_seq t1 t2) =
                  true →
                (!Prosa.Behavior.Service.scheduled_at online_sched j t1) = true) →
            ∃ j,
              decide
                    (j ∈
                      Prosa.Results.TransferSchedulability.Criterion.critical_jobs ref_sched online_sched ref_job_cost
                        online_job_cost arr_seq t1 t2) =
                  true ∧
                (!Prosa.Behavior.Service.completed_by online_sched j t2) = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_delay_if_no_critical_job_is_scheduled
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
       forall t1 t2 : Nat,
       @eq Bool
         (Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job
            inst_3 ref_sched
            online_sched ref_job_cost online_job_cost arr_seq online_job_cost t1 t2)
         Bool_true ->
       (forall j : Job,
        @eq Bool
          (Decidable_decide
             (Membership_mem Job (List Job) (List_instMembership Job)
                (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                   inst_3
                   ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
                j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_3)
                (instLawfulBEq Job
                   inst_3)
                j
                (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                   inst_3
                   ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)))
          Bool_true ->
        @eq Bool
          (Bool_not
             (Prosa_Behavior_Service_scheduled_at_inst4 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)
                online_sched j t1))
          Bool_true) ->
       Exists Job
         (fun j : Job =>
          And
            (@eq Bool
               (Decidable_decide
                  (Membership_mem Job (List Job) (List_instMembership Job)
                     (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                        inst_3
                        ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
                     j)
                  (List_instDecidableMemOfLawfulBEq Job
                     (instBEqOfDecidableEq Job
                        inst_3)
                     (instLawfulBEq Job
                        inst_3)
                     j
                     (Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job
                        inst_3
                        ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)))
               Bool_true)
            (@eq Bool
               (Bool_not
                  (Prosa_Behavior_Service_completed_by_inst4 Job
                     inst_3
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3)
                     online_sched online_job_cost j t2))
               Bool_true))
```
