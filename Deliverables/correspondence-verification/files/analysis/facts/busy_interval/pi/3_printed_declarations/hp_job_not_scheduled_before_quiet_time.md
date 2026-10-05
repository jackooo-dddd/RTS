# `hp_job_not_scheduled_before_quiet_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.hp_job_not_scheduled_before_quiet_time`
- Certificate: `hp_job_not_scheduled_before_quiet_time_correspondence`

## Official Rocq

```coq
hp_job_not_scheduled_before_quiet_time :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState) {JLFP : JLFP_policy Job}
  {JobReady0 : @JobReady Job PState H2 H1},
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall (j jhp : Equality.sort Job) (t : nat),
@quiet_time Job H1 H2 PState arr_seq sched JLFP j t.+1 ->
is_true (@scheduled_at Job PState sched jhp t.+1) ->
is_true (@hep_job Job JLFP jhp j) -> is_true (~~ @scheduled_at Job PState sched jhp t)

hp_job_not_scheduled_before_quiet_time is not universe polymorphic
Arguments hp_job_not_scheduled_before_quiet_time {Job H1 H2} arr_seq {PState} sched 
  {JLFP JobReady0} H_sched_valid j jhp t%nat_scope _ _ _
hp_job_not_scheduled_before_quiet_time is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time
Declared in library prosa.analysis.facts.busy_interval.pi, line 369, characters 10-48
@hp_job_not_scheduled_before_quiet_time
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (JobReady0 : @JobReady Job PState H2 H1),
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall (j jhp : Equality.sort Job) (t : nat),
       @quiet_time Job H1 H2 PState arr_seq sched JLFP j t.+1 ->
       is_true (@scheduled_at Job PState sched jhp t.+1) ->
       is_true (@hep_job Job JLFP jhp j) -> is_true (~~ @scheduled_at Job PState sched jhp t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.hp_job_not_scheduled_before_quiet_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
  [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
    ∀ (j jhp : Job) (t : ℕ),
      Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j (t + 1) →
        Prosa.Behavior.Service.scheduled_at sched jhp (t + 1) = true →
          Prosa.Model.Priority.Definitions.hep_job jhp j = true →
            (!Prosa.Behavior.Service.scheduled_at sched jhp t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_hp_job_not_scheduled_before_quiet_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_20 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_20 arr_seq ->
       forall (j jhp : Job) (t : Nat),
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched JLFP
         j
         (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jhp
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3 JLFP jhp j)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched jhp t))
         Bool_true
```
