# `exists_busy_interval_prefix`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.exists_busy_interval_prefix`
- Certificate: `exists_busy_interval_prefix_correspondence`

## Official Rocq

```coq
exists_busy_interval_prefix :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState) {JLFP : JLFP_policy Job}
  (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
@reflexive_job_priorities Job JLFP ->
forall t_busy : instant,
is_true (@pending Job PState sched Cost Arrival j t_busy) ->
exists t1 : instant,
  (fun t2 : instant => [eta @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t2]) t1
    t_busy.+1 /\
  is_true (t1 <= @job_arrival Job Arrival j <= t_busy)

exists_busy_interval_prefix is not universe polymorphic
Arguments exists_busy_interval_prefix {Job Arrival Cost} arr_seq H_valid_arrival_time 
  {PState} sched {JLFP} j H_from_arrival_sequence H_priority_is_reflexive t_busy 
  H_j_is_pending
exists_busy_interval_prefix is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix
Declared in library prosa.analysis.facts.busy_interval.existence, line 372, characters 12-39
@exists_busy_interval_prefix
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       @reflexive_job_priorities Job JLFP ->
       forall t_busy : instant,
       is_true (@pending Job PState sched Cost Arrival j t_busy) ->
       exists t1 : instant,
         @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t_busy.+1 /\
         is_true (t1 <= @job_arrival Job Arrival j <= t_busy)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.exists_busy_interval_prefix : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
      (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
          ∀ (t_busy : Prosa.Behavior.Time.instant),
            Prosa.Behavior.Service.pending sched j t_busy = true →
              ∃ t1,
                Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 (t_busy + 1) ∧
                  (decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) &&
                      decide (Prosa.Behavior.Job.job_arrival j ≤ t_busy)) =
                    true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_exists_busy_interval_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall t_busy : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_9
            inst_6 j t_busy)
         Bool_true ->
       Exists Prosa_Behavior_Time_instant
         (fun t1 : Prosa_Behavior_Time_instant =>
          And
            (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
               inst_3
               inst_6
               inst_9 PState
               arr_seq sched JLFP j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t_busy
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
            (@eq Bool
               (Bool_and
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_6 j))
                     (Nat_decLe t1
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_6 j)))
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_6 j)
                        t_busy)
                     (Nat_decLe
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_6 j)
                        t_busy)))
               Bool_true))
```
