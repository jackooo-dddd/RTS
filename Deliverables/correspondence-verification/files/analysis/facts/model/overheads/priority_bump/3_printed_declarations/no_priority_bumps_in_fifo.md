# `no_priority_bumps_in_fifo`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.PriorityBump.no_priority_bumps_in_fifo`
- Certificate: `no_priority_bumps_in_fifo_correspondence`

## Official Rocq

```coq
no_priority_bumps_in_fifo :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@transitive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H (processor_state Job) sched H0 (@basic_ready_instance Job (processor_state Job) H H0)
  arr_seq ->
@work_conserving Job H H0 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H H0)
  arr_seq sched ->
forall {H1 : JobPreemptable Job},
@valid_preemption_model Job H0 H1 (processor_state Job) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H H0 (processor_state Job) H1
  (@basic_ready_instance Job (processor_state Job) H H0) arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H0 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H H0 (processor_state Job) arr_seq sched JLFP j t1 t2 ->
(forall j1 j2 : Equality.sort Job, @hep_job Job JLFP j1 j2 = (@job_arrival Job H j1 <= @job_arrival Job H j2)) ->
forall t : instant, is_true (t1 < t <= t2) -> is_true (~~ @priority_bump Job JLFP sched t)

no_priority_bumps_in_fifo is not universe polymorphic
Arguments no_priority_bumps_in_fifo {Job H H0 JLFP} H_priority_is_reflexive H_priority_is_transitive 
  arr_seq H_valid_arrival_sequence sched H_valid_schedule H_work_conserving {H1} 
  H_valid_preemption_model H_respects_policy j H_from_arrival_sequence H_job_cost_positive 
  t1 t2 H_busy_interval_prefix H_JLFP_is_FIFO%function_scope t _
no_priority_bumps_in_fifo is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo
Declared in library prosa.analysis.facts.model.overheads.priority_bump, line 114, characters 8-33
@no_priority_bumps_in_fifo
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       @transitive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H (processor_state Job) sched H0
         (@basic_ready_instance Job (processor_state Job) H H0) arr_seq ->
       @work_conserving Job H H0 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H H0)
         arr_seq sched ->
       forall H1 : JobPreemptable Job,
       @valid_preemption_model Job H0 H1 (processor_state Job) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H H0 (processor_state Job) H1
         (@basic_ready_instance Job (processor_state Job) H H0) arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H0 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H H0 (processor_state Job) arr_seq sched JLFP j t1 t2 ->
       (forall j1 j2 : Equality.sort Job,
        @hep_job Job JLFP j1 j2 = (@job_arrival Job H j1 <= @job_arrival Job H j2)) ->
       forall t : instant, is_true (t1 < t <= t2) -> is_true (~~ @priority_bump Job JLFP sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.PriorityBump.no_priority_bumps_in_fifo : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                    Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                      ∀ (j : Job),
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                          Prosa.Model.Job.Properties.job_cost_positive j = true →
                            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                              Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
                                  t2 →
                                (∀ (j1 j2 : Job),
                                    Prosa.Model.Priority.Definitions.hep_job j1 j2 =
                                      decide (Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2)) →
                                  ∀ (t : Prosa.Behavior.Time.instant),
                                    (decide (t1 < t) && decide (t ≤ t2)) = true →
                                      (!Prosa.Analysis.Definitions.Overheads.PriorityBump.priority_bump sched t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_PriorityBump_no_priority_bumps_in_fifo
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
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_3
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_3),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         sched inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq sched ->
       forall
         inst_60 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_3
         inst_9
         inst_60
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         inst_60
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq sched JLFP ->
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
       (forall j1 j2 : Job,
        @eq Bool
          (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
             inst_3 JLFP j1
             j2)
          (Decidable_decide
             (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_3
                   inst_6 j1)
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_3
                   inst_6 j2))
             (Nat_decLe
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_3
                   inst_6 j1)
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_3
                   inst_6 j2)))) ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump Job
               inst_3 JLFP
               sched t))
         Bool_true
```
