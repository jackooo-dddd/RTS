# `service_of_jobs_always_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_of_jobs_always_scheduled`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_always_scheduled`
- Certificate: `service_of_jobs_always_scheduled_correspondence`

## Official Rocq

```coq
service_of_jobs_always_scheduled :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)),
@ideal_progress_proc_model Job PState ->
forall js : seq (Equality.sort Job),
is_true (@uniq Job js) ->
forall t1 t2 : nat,
(forall t : nat,
 is_true (t1 <= t < t2) ->
 exists j : Equality.sort Job,
   is_true (j \in js) /\ is_true (@scheduled_at Job PState sched j t) /\ is_true (P j)) ->
@service_of_jobs Job PState sched P js t1 t2 = t2 - t1

service_of_jobs_always_scheduled is not universe polymorphic
Arguments service_of_jobs_always_scheduled {Job PState} H_unit_service_proc_model 
  H_uniprocessor_model sched P H_ideal_progress_model js%seq_scope H_no_duplicate_jobs 
  (t1 t2)%nat_scope _%function_scope
service_of_jobs_always_scheduled is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_of_jobs_always_scheduled
Declared in library prosa.analysis.facts.model.service_of_jobs, line 580, characters 10-42
@service_of_jobs_always_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)),
       @ideal_progress_proc_model Job PState ->
       forall js : seq (Equality.sort Job),
       is_true (@uniq Job js) ->
       forall t1 t2 : nat,
       (forall t : nat,
        is_true (t1 <= t < t2) ->
        exists j : Equality.sort Job,
          is_true (j \in js) /\ is_true (@scheduled_at Job PState sched j t) /\ is_true (P j)) ->
       @service_of_jobs Job PState sched P js t1 t2 = t2 - t1
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_always_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
      ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool),
        Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
          ∀ (js : List Job),
            js.Nodup →
              ∀ (t1 t2 : ℕ),
                (∀ (t : ℕ),
                    (decide (t1 ≤ t) && decide (t < t2)) = true →
                      ∃ j, decide (j ∈ js) = true ∧ Prosa.Behavior.Service.scheduled_at sched j t = true ∧ P j = true) →
                  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched P js t1 t2 = t2 - t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_always_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall js : List Job,
       List_Nodup Job js ->
       forall t1 t2 : Nat,
       (forall t : Nat,
        @eq Bool
          (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
          Bool_true ->
        Exists Job
          (fun j : Job =>
           And
             (@eq Bool
                (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) js j)
                   (List_instDecidableMemOfLawfulBEq Job
                      (instBEqOfDecidableEq Job
                         inst_3)
                      (instLawfulBEq Job
                         inst_3)
                      j js))
                Bool_true)
             (And
                (@eq Bool
                   (Prosa_Behavior_Service_scheduled_at Job
                      inst_3 PState
                      sched j t)
                   Bool_true)
                (@eq Bool (P j) Bool_true)))) ->
       @eq Nat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
            inst_3 PState sched P js
            t1 t2)
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) t2 t1)
```
