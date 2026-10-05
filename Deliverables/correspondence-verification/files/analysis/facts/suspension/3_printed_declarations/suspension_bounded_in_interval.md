# `suspension_bounded_in_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.suspension.suspension_bounded_in_interval`
- Lean: `Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval`
- Certificate: `suspension_bounded_in_interval_correspondence`

## Official Rocq

```coq
suspension_bounded_in_interval :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobSuspension Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t1 t2 : instant) (ρ : work),
is_true
  (\sum_(t1 <= t < t2 | @service Job PState sched j t == ρ)
      nat_of_bool (@suspended Job PState H H0 H1 sched j t) <=
   @job_suspension Job H1 j ρ)

suspension_bounded_in_interval is not universe polymorphic
Arguments suspension_bounded_in_interval {Job H H0 H1 PState} sched j t1 t2 ρ
suspension_bounded_in_interval is opaque
Expands to: Constant prosa.analysis.facts.suspension.suspension_bounded_in_interval
Declared in library prosa.analysis.facts.suspension, line 265, characters 10-40
@suspension_bounded_in_interval
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobSuspension Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (j : Equality.sort Job)
         (t1 t2 : instant) (ρ : work),
       is_true
         (\sum_(t1 <= t < t2 | @service Job PState sched j t == ρ)
             nat_of_bool (@suspended Job PState H H0 H1 sched j t) <=
          @job_suspension Job H1 j ρ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Readiness.Suspension.JobSuspension Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant)
  (ρ : Prosa.Behavior.Job.work),
  (∑ t ∈ Finset.Ico t1 t2,
      if Prosa.Behavior.Service.service sched j t = ρ then (Prosa.Model.Readiness.Suspension.suspended sched j t).toNat
      else 0) ≤
    Prosa.Model.Readiness.Suspension.job_suspension j ρ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Suspension_suspension_bounded_in_interval
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job inst_3)
         (inst_12 : 
          Prosa_Model_Readiness_Suspension_JobSuspension Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) (_UU03c1_ : Prosa_Behavior_Job_work),
       LE_le_inst1 Nat instLENat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t : Nat =>
                ite Nat
                  (@eq Prosa_Behavior_Job_work
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched j t)
                     _UU03c1_)
                  (instDecidableEqNat
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched j t)
                     _UU03c1_)
                  (Bool_toNat
                     (Prosa_Model_Readiness_Suspension_suspended Job
                        inst_3 PState
                        inst_6
                        inst_9
                        inst_12 sched j t))
                  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
               (List_range' t1 (Nat_sub t2 t1) 1)))
         (Prosa_Model_Readiness_Suspension_JobSuspension_job_suspension Job
            inst_3
            inst_12 j _UU03c1_)
```
