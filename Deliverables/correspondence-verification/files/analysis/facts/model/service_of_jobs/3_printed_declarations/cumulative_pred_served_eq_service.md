# `cumulative_pred_served_eq_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.cumulative_pred_served_eq_service`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.cumulative_pred_served_eq_service`
- Certificate: `cumulative_pred_served_eq_service_correspondence`

## Official Rocq

```coq
cumulative_pred_served_eq_service :
forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
@uniprocessor_model Job PState ->
forall arr_seq : arrival_sequence Job,
@consistent_arrival_times Job H0 arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H0 PState sched ->
@completed_jobs_dont_execute Job PState sched H1 ->
forall P : pred (Equality.sort Job),
@arrival_sequence_uniq Job arr_seq ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t1 t : instant),
@quiet_time Job H0 H1 PState arr_seq sched JLFP j t1 ->
(forall j' : Equality.sort Job, is_true (P j') -> is_true (@hep_job Job JLFP j' j)) ->
\sum_(t1 <= t' < t) nat_of_bool (@has (Equality.sort Job) P (@served_jobs_at Job PState arr_seq sched t')) =
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t1 t

cumulative_pred_served_eq_service is not universe polymorphic
Arguments cumulative_pred_served_eq_service {Job H0 H1 PState} H_unit_service_proc_model 
  H_uniprocessor_model arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute P H_arrival_sequence_is_a_set {JLFP} j t1 t H_quiet_time 
  _%function_scope
cumulative_pred_served_eq_service is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.cumulative_pred_served_eq_service
Declared in library prosa.analysis.facts.model.service_of_jobs, line 628, characters 10-43
@cumulative_pred_served_eq_service
     : forall (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       @uniprocessor_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @consistent_arrival_times Job H0 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       @completed_jobs_dont_execute Job PState sched H1 ->
       forall P : pred (Equality.sort Job),
       @arrival_sequence_uniq Job arr_seq ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t1 t : instant),
       @quiet_time Job H0 H1 PState arr_seq sched JLFP j t1 ->
       (forall j' : Equality.sort Job, is_true (P j') -> is_true (@hep_job Job JLFP j' j)) ->
       \sum_(t1 <= t' < t)
          nat_of_bool (@has (Equality.sort Job) P (@served_jobs_at Job PState arr_seq sched t')) =
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t) t1 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.cumulative_pred_served_eq_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
              Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                ∀ (P : Job → Bool),
                  Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
                    ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job)
                      (t1 t : Prosa.Behavior.Time.instant),
                      Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t1 →
                        (∀ (j' : Job), P j' = true → Prosa.Model.Priority.Definitions.hep_job j' j = true) →
                          ∑ t' ∈ Finset.Ico t1 t,
                              ((Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t').any P).toNat =
                            Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
                              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t) t1 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_cumulative_pred_served_eq_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_9 ->
       forall P : Job -> Bool,
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t1 t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched
         JLFP j t1 ->
       (forall j' : Job,
        @eq Bool (P j') Bool_true ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
             inst_3 JLFP j' j)
          Bool_true) ->
       @eq Nat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t' : Nat =>
                Bool_toNat
                  (List_any Job
                     (Prosa_Analysis_Definitions_Service_served_jobs_at Job
                        inst_3 PState
                        arr_seq sched t')
                     P))
               (List_range' t1 (Nat_sub t t1) 1)))
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t)
            t1 t)
```
