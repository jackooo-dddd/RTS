# `job_scheduled_in_busy_interval_prefix`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Schedule.job_scheduled_in_busy_interval_prefix`
- Certificate: `job_scheduled_in_busy_interval_prefix_correspondence`

## Official Rocq

```coq
job_scheduled_in_busy_interval_prefix :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall (sched : @schedule Job (overheads.processor_state Job))
  {JobReady0 : @JobReady Job (overheads.processor_state Job) H0 H},
@work_bearing_readiness Job H H0 (overheads.processor_state Job) JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H (overheads.processor_state Job) sched H0 JobReady0 arr_seq ->
@work_conserving Job H H0 (overheads.processor_state Job) JobReady0 arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H0 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H H0 (overheads.processor_state Job) arr_seq sched JLFP j t1 t2 ->
forall t : nat,
is_true (t1 <= t < t2) ->
exists jo : Equality.sort Job, is_true (@scheduled_at Job (overheads.processor_state Job) sched jo t)

job_scheduled_in_busy_interval_prefix is not universe polymorphic
Arguments job_scheduled_in_busy_interval_prefix {Job H H0 JLFP} H_priority_is_reflexive 
  arr_seq H_valid_arrival_sequence sched {JobReady0} H_job_ready H_sched_valid H_work_conserving 
  j H_from_arrival_sequence H_job_cost_positive t1 t2 H_busy_interval_prefix t%nat_scope 
  _
job_scheduled_in_busy_interval_prefix is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix
Declared in library prosa.analysis.facts.model.overheads.schedule, line 157, characters 8-45
@job_scheduled_in_busy_interval_prefix
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall (sched : @schedule Job (overheads.processor_state Job))
         (JobReady0 : @JobReady Job (overheads.processor_state Job) H0 H),
       @work_bearing_readiness Job H H0 (overheads.processor_state Job) JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H (overheads.processor_state Job) sched H0 JobReady0 arr_seq ->
       @work_conserving Job H H0 (overheads.processor_state Job) JobReady0 arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H0 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H H0 (overheads.processor_state Job) arr_seq sched JLFP j t1 t2 ->
       forall t : nat,
       is_true (t1 <= t < t2) ->
       exists jo : Equality.sort Job, is_true (@scheduled_at Job (overheads.processor_state Job) sched jo t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Schedule.job_scheduled_in_busy_interval_prefix : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
          [inst_3 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Overheads.processor_state Job)],
          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                ∀ (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Model.Job.Properties.job_cost_positive j = true →
                      ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                          ∀ (t : ℕ),
                            (decide (t1 ≤ t) && decide (t < t2)) = true →
                              ∃ jo, Prosa.Behavior.Service.scheduled_at sched jo t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Schedule_job_scheduled_in_busy_interval_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (inst_33 : 
          Prosa_Behavior_Ready_JobReady_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         inst_33 arr_seq sched
         JLFP ->
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         sched inst_9
         inst_33 arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         inst_33 arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         arr_seq sched JLFP j t1 t2 ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       Exists Job
         (fun jo : Job =>
          Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            sched jo t =
          Bool_true)
```
