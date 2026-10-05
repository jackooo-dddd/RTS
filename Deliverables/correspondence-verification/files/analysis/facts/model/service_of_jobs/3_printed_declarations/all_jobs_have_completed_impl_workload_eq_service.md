# `all_jobs_have_completed_impl_workload_eq_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_impl_workload_eq_service`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.all_jobs_have_completed_impl_workload_eq_service`
- Certificate: `all_jobs_have_completed_impl_workload_eq_service_correspondence`

## Official Rocq

```coq
all_jobs_have_completed_impl_workload_eq_service :
forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@consistent_arrival_times Job H0 arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H0 PState sched ->
@completed_jobs_dont_execute Job PState sched H1 ->
forall (P : pred (Equality.sort Job)) (t1 t2 t_compl : instant),
(fun t_compl0 : instant =>
 forall j : Equality.sort Job,
 is_true (j \in @arrivals_between Job arr_seq t1 t2) ->
 is_true (P j) -> is_true (@completed_by Job PState sched H1 j t_compl0)) t_compl ->
@workload_of_jobs Job H1 P (@arrivals_between Job arr_seq t1 t2) =
@service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t2) t1 t_compl

all_jobs_have_completed_impl_workload_eq_service is not universe polymorphic
Arguments all_jobs_have_completed_impl_workload_eq_service {Job H0 H1 PState} H_unit_service_proc_model
  arr_seq H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  P t1 t2 t_compl _%function_scope
all_jobs_have_completed_impl_workload_eq_service is opaque
Expands to: Constant
            prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_impl_workload_eq_service
Declared in library prosa.analysis.facts.model.service_of_jobs, line 385, characters 10-58
@all_jobs_have_completed_impl_workload_eq_service
     : forall (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @consistent_arrival_times Job H0 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       @completed_jobs_dont_execute Job PState sched H1 ->
       forall (P : pred (Equality.sort Job)) (t1 t2 t_compl : instant),
       (forall j : Equality.sort Job,
        is_true (j \in @arrivals_between Job arr_seq t1 t2) ->
        is_true (P j) -> is_true (@completed_by Job PState sched H1 j t_compl)) ->
       @workload_of_jobs Job H1 P (@arrivals_between Job arr_seq t1 t2) =
       @service_of_jobs Job PState sched P (@arrivals_between Job arr_seq t1 t2) t1 t_compl
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.all_jobs_have_completed_impl_workload_eq_service : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
            Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
              ∀ (P : Job → Bool) (t1 t2 t_compl : Prosa.Behavior.Time.instant),
                (∀ (j : Job),
                    decide (j ∈ Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) = true →
                      P j = true → Prosa.Behavior.Service.completed_by sched j t_compl = true) →
                  Prosa.Model.Aggregate.Workload.workload_of_jobs P
                      (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
                    Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P
                      (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) t1 t_compl
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_all_jobs_have_completed_impl_workload_eq_service
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
       forall (P : Job -> Bool) (t1 t2 t_compl : Prosa_Behavior_Time_instant),
       (forall j : Job,
        @eq Bool
          (Decidable_decide
             (Membership_mem Job (List Job) (List_instMembership Job)
                (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                   inst_3 arr_seq t1
                   t2)
                j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_3)
                (instLawfulBEq Job
                   inst_3)
                j
                (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                   inst_3 arr_seq t1
                   t2)))
          Bool_true ->
        @eq Bool (P j) Bool_true ->
        @eq Bool
          (Prosa_Behavior_Service_completed_by Job
             inst_3 PState sched
             inst_9 j t_compl)
          Bool_true) ->
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_9 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2))
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2)
            t1 t_compl)
```
