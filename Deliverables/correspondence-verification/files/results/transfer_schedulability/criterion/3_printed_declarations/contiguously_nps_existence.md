# `contiguously_nps_existence`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.contiguously_nps_existence`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.contiguously_nps_existence`
- Certificate: `contiguously_nps_existence_correspondence`

## Official Rocq

```coq
contiguously_nps_existence :
forall {Job : JobType} {H : JobArrival Job}
  (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) ref_sched arr_seq ->
@jobs_must_arrive_to_execute Job H (ideal.processor_state Job) ref_sched ->
forall job_cost_bound : JobCost Job,
(forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
(forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
forall (j : Equality.sort Job) (t2 : instant),
is_true (@completed_by Job (ideal.processor_state Job) ref_sched ref_job_cost j t2) ->
is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t2) ->
exists t1 : nat,
  is_true
    (@contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2) /\
  is_true (t1 < t2) /\
  (t1 = 0 \/
   is_true
     (~~
      @nonpositive_slack Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1.-1
        t2))

contiguously_nps_existence is not universe polymorphic
Arguments contiguously_nps_existence {Job H} ref_sched online_sched ref_job_cost 
  online_job_cost arr_seq H_valid_arrivals H_jobs_arr_ref H_jobs_must_arrive_ref 
  job_cost_bound (H_job_cost_bounded H_ref_cost_dominates)%function_scope j t2 _ 
  _
contiguously_nps_existence is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.contiguously_nps_existence
Declared in library prosa.results.transfer_schedulability.criterion, line 708, characters 10-36
@contiguously_nps_existence
     : forall (Job : JobType) (H : JobArrival Job)
         (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) ref_sched arr_seq ->
       @jobs_must_arrive_to_execute Job H (ideal.processor_state Job) ref_sched ->
       forall job_cost_bound : JobCost Job,
       (forall j : Equality.sort Job, is_true (online_job_cost j <= job_cost_bound j)) ->
       (forall j : Equality.sort Job, is_true (job_cost_bound j <= ref_job_cost j)) ->
       forall (j : Equality.sort Job) (t2 : instant),
       is_true (@completed_by Job (ideal.processor_state Job) ref_sched ref_job_cost j t2) ->
       is_true (~~ @completed_by Job (ideal.processor_state Job) online_sched online_job_cost j t2) ->
       exists t1 : nat,
         is_true
           (@contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
              t1 t2) /\
         is_true (t1 < t2) /\
         (t1 = 0 \/
          is_true
            (~~
             @nonpositive_slack Job ref_sched online_sched ref_job_cost online_job_cost arr_seq
               job_cost_bound t1.-1 t2))
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.contiguously_nps_existence : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence ref_sched arr_seq →
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute ref_sched →
        ∀ (job_cost_bound : Prosa.Behavior.Job.JobCost Job),
          (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
            (∀ (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
              ∀ (j : Job) (t2 : Prosa.Behavior.Time.instant),
                Prosa.Behavior.Service.completed_by ref_sched j t2 = true →
                  (!Prosa.Behavior.Service.completed_by online_sched j t2) = true →
                    ∃ t1,
                      Prosa.Results.TransferSchedulability.Criterion.contiguously_nps ref_sched online_sched
                            ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 =
                          true ∧
                        t1 < t2 ∧
                          (t1 = 0 ∨
                            (!Prosa.Results.TransferSchedulability.Criterion.nonpositive_slack ref_sched online_sched
                                  ref_job_cost online_job_cost arr_seq job_cost_bound (t1 - 1) t2) =
                              true)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_contiguously_nps_existence
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
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         ref_sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         ref_sched ->
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
       (forall j : Job,
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             job_cost_bound j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3 ref_job_cost
             j)) ->
       forall (j : Job) (t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_completed_by_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            ref_sched ref_job_cost j t2)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               online_sched online_job_cost j t2))
         Bool_true ->
       Exists Nat
         (fun t1 : Nat =>
          And
            (@eq Bool
               (Prosa_Results_TransferSchedulability_Criterion_contiguously_nps Job
                  inst_3
                  ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2)
               Bool_true)
            (And (LT_lt_inst1 Nat instLTNat t1 t2)
               (Or (@eq Nat t1 (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
                  (@eq Bool
                     (Bool_not
                        (Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack Job
                           inst_3
                           ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
                           (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t1
                              (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                           t2))
                     Bool_true))))
```
