# `priority_higher_than_pending_job_priority`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.preemption.priority_higher_than_pending_job_priority`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.priority_higher_than_pending_job_priority`
- Certificate: `priority_higher_than_pending_job_priority_correspondence`

## Official Rocq

```coq
priority_higher_than_pending_job_priority :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall {JobReady0 : @JobReady Job PState Cost Arrival} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall (sched : @schedule Job PState) {H : JobPreemptable Job},
@valid_preemption_model Job Cost H PState arr_seq sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@valid_schedule Job Arrival PState sched Cost JobReady0 arr_seq ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H JobReady0 arr_seq sched JLFP ->
forall (j : Equality.sort Job) (t1 t2 : instant),
is_true (@scheduled_at Job PState sched j t1) ->
is_true (@scheduled_at Job PState sched j t2) ->
(forall t : nat, is_true (t1 <= t < t2) -> is_true (@job_ready Job PState Cost Arrival JobReady0 sched j t)) ->
forall t : instant,
is_true (t1 <= t < t2) ->
forall jhp : Equality.sort Job,
is_true (@scheduled_at Job PState sched jhp t) -> is_true (@hep_job Job JLFP jhp j)

priority_higher_than_pending_job_priority is not universe polymorphic
Arguments priority_higher_than_pending_job_priority {Job Arrival Cost PState} H_uniproc 
  {JobReady0} arr_seq H_valid_arrivals sched {H} H_valid_preemption_model {JLFP} 
  H_priority_is_reflexive H_valid_schedule H_respects_policy j t1 t2 H_sched_t1 H_sched_t2
  H_j_is_ready%function_scope t _ jhp _
priority_higher_than_pending_job_priority is opaque
Expands to: Constant prosa.analysis.facts.model.preemption.priority_higher_than_pending_job_priority
Declared in library prosa.analysis.facts.model.preemption, line 385, characters 12-53
@priority_higher_than_pending_job_priority
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (JobReady0 : @JobReady Job PState Cost Arrival) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (sched : @schedule Job PState) (H : JobPreemptable Job),
       @valid_preemption_model Job Cost H PState arr_seq sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       @valid_schedule Job Arrival PState sched Cost JobReady0 arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H JobReady0 arr_seq sched JLFP ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       is_true (@scheduled_at Job PState sched j t1) ->
       is_true (@scheduled_at Job PState sched j t2) ->
       (forall t : nat,
        is_true (t1 <= t < t2) -> is_true (@job_ready Job PState Cost Arrival JobReady0 sched j t)) ->
       forall t : instant,
       is_true (t1 <= t < t2) ->
       forall jhp : Equality.sort Job,
       is_true (@scheduled_at Job PState sched jhp t) -> is_true (@hep_job Job JLFP jhp j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.priority_higher_than_pending_job_priority : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ [inst_3 : Prosa.Behavior.Ready.JobReady Job PState]
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState)
          [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
          Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
            ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
              Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                  Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
                      Prosa.Behavior.Service.scheduled_at sched j t1 = true →
                        Prosa.Behavior.Service.scheduled_at sched j t2 = true →
                          (∀ (t : ℕ),
                              (decide (t1 ≤ t) && decide (t < t2)) = true →
                                Prosa.Behavior.Ready.job_ready sched j t = true) →
                            ∀ (t : Prosa.Behavior.Time.instant),
                              (decide (t1 ≤ t) && decide (t < t2)) = true →
                                ∀ (jhp : Job),
                                  Prosa.Behavior.Service.scheduled_at sched jhp t = true →
                                    Prosa.Model.Priority.Definitions.hep_job jhp j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_priority_higher_than_pending_job_priority
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (inst_19 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_32 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_32 PState arr_seq sched ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_19 arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_32
         inst_19 arr_seq sched JLFP ->
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t1)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t2)
         Bool_true ->
       (forall t : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
          Bool_true ->
        @eq Bool
          (Prosa_Behavior_Ready_JobReady_job_ready Job
             inst_3 PState
             inst_9
             inst_6
             inst_19 sched j t)
          Bool_true) ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       forall jhp : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jhp t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3 JLFP jhp j)
         Bool_true
```
