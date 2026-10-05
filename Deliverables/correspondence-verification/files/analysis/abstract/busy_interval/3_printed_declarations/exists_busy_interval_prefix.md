# `exists_busy_interval_prefix`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.exists_busy_interval_prefix`
- Certificate: `exists_busy_interval_prefix_correspondence`

## Official Rocq

```coq
exists_busy_interval_prefix :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t_busy : instant),
is_true (@pending Job PState sched H2 H1 j t_busy) ->
exists t1 : instant,
  @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t_busy.+1 /\
  is_true (t1 <= @job_arrival Job H1 j <= t_busy)

exists_busy_interval_prefix is not universe polymorphic
Arguments exists_busy_interval_prefix {Job H1 H2 PState H3 H4} sched j t_busy H_j_is_pending
exists_busy_interval_prefix is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix
Declared in library prosa.analysis.abstract.busy_interval, line 316, characters 10-37
@exists_busy_interval_prefix
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t_busy : instant),
       is_true (@pending Job PState sched H2 H1 j t_busy) ->
       exists t1 : instant,
         @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t_busy.+1 /\
         is_true (t1 <= @job_arrival Job H1 j <= t_busy)
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.exists_busy_interval_prefix : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t_busy : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.pending sched j t_busy = true →
    ∃ t1,
      Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 (t_busy + 1) ∧
        (decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) && decide (Prosa.Behavior.Job.job_arrival j ≤ t_busy)) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_exists_busy_interval_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (inst_22 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_25 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (j : Job) (t_busy : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_7 PState sched
            inst_17
            inst_14 j t_busy)
         Bool_true ->
       Exists Prosa_Behavior_Time_instant
         (fun t1 : Prosa_Behavior_Time_instant =>
          And
            (Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
               inst_7
               inst_22
               inst_25
               inst_14
               inst_17 PState sched j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t_busy
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
            (@eq Bool
               (Bool_and
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7
                           inst_14 j))
                     (Nat_decLe t1
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7
                           inst_14 j)))
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7
                           inst_14 j)
                        t_busy)
                     (Nat_decLe
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_7
                           inst_14 j)
                        t_busy)))
               Bool_true))
```
