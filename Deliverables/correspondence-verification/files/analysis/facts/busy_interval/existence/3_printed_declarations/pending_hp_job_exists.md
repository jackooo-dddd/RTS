# `pending_hp_job_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.pending_hp_job_exists`
- Certificate: `pending_hp_job_exists_correspondence`

## Official Rocq

```coq
pending_hp_job_exists :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job Arrival PState sched ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job Cost j) ->
@reflexive_job_priorities Job JLFP ->
forall t1 t2 : instant,
(fun t3 : instant => [eta @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t3]) t1 t2 ->
forall t : nat,
is_true (t1 <= t < t2) ->
exists jhp : Equality.sort Job,
  @arrives_in Job arr_seq jhp /\
  is_true (@pending Job PState sched Cost Arrival jhp t) /\ is_true (@hep_job Job JLFP jhp j)

pending_hp_job_exists is not universe polymorphic
Arguments pending_hp_job_exists {Job Arrival Cost} arr_seq H_valid_arrival_time {PState} 
  sched H_jobs_must_arrive_to_execute {JLFP} j H_from_arrival_sequence H_job_cost_positive
  H_priority_is_reflexive t1 t2 H_busy_interval_prefix t%nat_scope _
pending_hp_job_exists is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists
Declared in library prosa.analysis.facts.busy_interval.existence, line 165, characters 10-31
@pending_hp_job_exists
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job Arrival PState sched ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job Cost j) ->
       @reflexive_job_priorities Job JLFP ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
       forall t : nat,
       is_true (t1 <= t < t2) ->
       exists jhp : Equality.sort Job,
         @arrives_in Job arr_seq jhp /\
         is_true (@pending Job PState sched Cost Arrival jhp t) /\ is_true (@hep_job Job JLFP jhp j)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.pending_hp_job_exists : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            Prosa.Model.Job.Properties.job_cost_positive j = true →
              Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                  Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                    ∀ (t : ℕ),
                      (decide (t1 ≤ t) && decide (t < t2)) = true →
                        ∃ jhp,
                          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jhp ∧
                            Prosa.Behavior.Service.pending sched jhp t = true ∧
                              Prosa.Model.Priority.Definitions.hep_job jhp j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_pending_hp_job_exists
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
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
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
       Exists Job
         (fun jhp : Job =>
          And
            (Prosa_Behavior_Arrival_sequence_arrives_in Job
               inst_3 arr_seq jhp)
            (And
               (@eq Bool
                  (Prosa_Behavior_Service_pending Job
                     inst_3 PState
                     sched inst_9
                     inst_6 jhp t)
                  Bool_true)
               (@eq Bool
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_3 JLFP
                     jhp j)
                  Bool_true)))
```
