# `idle_instant_next_no_carry_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in`
- Lean: `Prosa.Analysis.Facts.BusyInterval.CarryIn.idle_instant_next_no_carry_in`
- Certificate: `idle_instant_next_no_carry_in_correspondence`

## Official Rocq

```coq
idle_instant_next_no_carry_in :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job} {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
forall t : instant,
is_true (@is_idle Job PState arr_seq sched t) -> @no_carry_in Job H1 H2 arr_seq PState sched t.+1

idle_instant_next_no_carry_in is not universe polymorphic
Arguments idle_instant_next_no_carry_in {Job H1 H2} arr_seq H_valid_arr_seq {PState} 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP JobReady0} 
  H_job_ready H_work_conserving t _ j_o _ _
idle_instant_next_no_carry_in is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in
Declared in library prosa.analysis.facts.busy_interval.carry_in, line 99, characters 8-37
@idle_instant_next_no_carry_in
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (JLFP : JLFP_policy Job) (JobReady0 : @JobReady Job PState H2 H1),
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       forall t : instant,
       is_true (@is_idle Job PState arr_seq sched t) -> @no_carry_in Job H1 H2 arr_seq PState sched t.+1
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.CarryIn.idle_instant_next_no_carry_in : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
            [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
            Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                ∀ (t : Prosa.Behavior.Time.instant),
                  Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
                    Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched (t + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_CarryIn_idle_instant_next_no_carry_in
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
         inst_3 PState sched arr_seq ->
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
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_6
         inst_9 PState
         inst_34 arr_seq sched ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq
            sched t)
         Bool_true ->
       Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
         inst_3
         inst_6
         inst_9 arr_seq PState sched
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
```
