# `not_quiet_implies_exists_pending_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.not_quiet_implies_exists_pending_job`
- Certificate: `not_quiet_implies_exists_pending_job_correspondence`

## Official Rocq

```coq
not_quiet_implies_exists_pending_job :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState) {JLFP : JLFP_policy Job}
  (j : Equality.sort Job) (t1 t2 : instant),
is_true (t1 <= t2) ->
~ [eta @quiet_time Job Arrival Cost PState arr_seq sched JLFP j] t2 ->
exists j_hp : Equality.sort Job,
  @arrives_in Job arr_seq j_hp /\
  is_true (@arrived_between Job Arrival j_hp t1 t2) /\
  is_true (@hep_job Job JLFP j_hp j) /\ ~ is_true (@completed_by Job PState sched Cost j_hp t2)

not_quiet_implies_exists_pending_job is not universe polymorphic
Arguments not_quiet_implies_exists_pending_job {Job Arrival Cost} arr_seq H_valid_arrival_time 
  {PState} sched {JLFP} j t1 t2 H_interval H_quiet H_not_quiet
not_quiet_implies_exists_pending_job is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job
Declared in library prosa.analysis.facts.busy_interval.existence, line 96, characters 10-46
@not_quiet_implies_exists_pending_job
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (j : Equality.sort Job) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       @quiet_time Job Arrival Cost PState arr_seq sched JLFP j t1 ->
       ~ @quiet_time Job Arrival Cost PState arr_seq sched JLFP j t2 ->
       exists j_hp : Equality.sort Job,
         @arrives_in Job arr_seq j_hp /\
         is_true (@arrived_between Job Arrival j_hp t1 t2) /\
         is_true (@hep_job Job JLFP j_hp j) /\ ~ is_true (@completed_by Job PState sched Cost j_hp t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.not_quiet_implies_exists_pending_job : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
      (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      t1 ≤ t2 →
        Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t1 →
          ¬Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t2 →
            ∃ j_hp,
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j_hp ∧
                Prosa.Behavior.Arrival_sequence.arrived_between j_hp t1 t2 = true ∧
                  Prosa.Model.Priority.Definitions.hep_job j_hp j = true ∧
                    ¬Prosa.Behavior.Service.completed_by sched j_hp t2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_not_quiet_implies_exists_pending_job
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
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched JLFP j t1 ->
       Not
         (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
            inst_3
            inst_6
            inst_9 PState arr_seq
            sched JLFP j t2) ->
       Exists Job
         (fun j_hp : Job =>
          And
            (Prosa_Behavior_Arrival_sequence_arrives_in Job
               inst_3 arr_seq j_hp)
            (And
               (@eq Bool
                  (Prosa_Behavior_Arrival_sequence_arrived_between Job
                     inst_3
                     inst_6 j_hp t1
                     t2)
                  Bool_true)
               (And
                  (@eq Bool
                     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                        inst_3 JLFP
                        j_hp j)
                     Bool_true)
                  (Not
                     (@eq Bool
                        (Prosa_Behavior_Service_completed_by Job
                           inst_3
                           PState sched
                           inst_9
                           j_hp t2)
                        Bool_true)))))
```
