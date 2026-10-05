# `not_quiet_implies_not_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.not_quiet_implies_not_idle`
- Certificate: `not_quiet_implies_not_idle_correspondence`

## Official Rocq

```coq
not_quiet_implies_not_idle :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job Arrival PState sched ->
forall {JLFP : JLFP_policy Job} {H0 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job Cost j) ->
@work_conserving Job Arrival Cost PState H0 arr_seq sched ->
@reflexive_job_priorities Job JLFP ->
forall t1 t2 : instant,
(fun t3 : instant => [eta @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t3]) t1 t2 ->
forall t : nat, is_true (t1 <= t < t2) -> ~ is_true (@is_idle Job PState arr_seq sched t)

not_quiet_implies_not_idle is not universe polymorphic
Arguments not_quiet_implies_not_idle {Job Arrival Cost} arr_seq H_valid_arrival_time 
  {PState} sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute 
  {JLFP H0} H_job_ready j H_from_arrival_sequence H_job_cost_positive H_work_conserving
  H_priority_is_reflexive t1 t2 H_busy_interval_prefix t%nat_scope _ _
not_quiet_implies_not_idle is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle
Declared in library prosa.analysis.facts.busy_interval.existence, line 215, characters 10-36
@not_quiet_implies_not_idle
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job Arrival PState sched ->
       forall (JLFP : JLFP_policy Job) (H0 : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job Cost j) ->
       @work_conserving Job Arrival Cost PState H0 arr_seq sched ->
       @reflexive_job_priorities Job JLFP ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
       forall t : nat, is_true (t1 <= t < t2) -> ~ is_true (@is_idle Job PState arr_seq sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.not_quiet_implies_not_idle : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
            [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
            Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
              ∀ (j : Job),
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                  Prosa.Model.Job.Properties.job_cost_positive j = true →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                          Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                            ∀ (t : ℕ),
                              (decide (t1 ≤ t) && decide (t < t2)) = true →
                                ¬Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_not_quiet_implies_not_idle
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
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_34 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched JLFP j t1 t2 ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       Not
         (@eq Bool
            (Prosa_Model_Schedule_Scheduled_is_idle Job
               inst_3 PState
               arr_seq sched t)
            Bool_true)
```
