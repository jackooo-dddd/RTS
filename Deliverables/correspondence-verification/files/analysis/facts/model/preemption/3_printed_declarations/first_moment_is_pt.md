# `first_moment_is_pt`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.first_moment_is_pt`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.first_moment_is_pt`
- Certificate: `first_moment_is_pt_correspondence`

## Official Rocq

```coq
first_moment_is_pt :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H PState sched ->
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall (j : Equality.sort Job) (prt : instant),
@arrives_in Job arr_seq j ->
is_true (~~ @scheduled_at Job PState sched j prt) ->
is_true (@scheduled_at Job PState sched j prt.+1) ->
is_true (@preemption_time Job H1 arr_seq PState sched prt.+1)

first_moment_is_pt is not universe polymorphic
Arguments first_moment_is_pt {Job H H0 H1} arr_seq H_valid_arrivals {PState} H_uniproc 
  sched H_jobs_come_from_arrival_sequence H_must_arrive H_valid_preemption_model 
  j prt _ _ _
first_moment_is_pt is opaque
Expands to: Constant prosa.analysis.facts.model.preemption.first_moment_is_pt
Declared in library prosa.analysis.facts.model.preemption, line 69, characters 8-26
@first_moment_is_pt
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H PState sched ->
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall (j : Equality.sort Job) (prt : instant),
       @arrives_in Job arr_seq j ->
       is_true (~~ @scheduled_at Job PState sched j prt) ->
       is_true (@scheduled_at Job PState sched j prt.+1) ->
       is_true (@preemption_time Job H1 arr_seq PState sched prt.+1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.first_moment_is_pt : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                ∀ (j : Job) (prt : Prosa.Behavior.Time.instant),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    (!Prosa.Behavior.Service.scheduled_at sched j prt) = true →
                      Prosa.Behavior.Service.scheduled_at sched j (prt + 1) = true →
                        Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched (prt + 1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_first_moment_is_pt
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_12 PState arr_seq sched ->
       forall (j : Job) (prt : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j prt))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) prt
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
            inst_3
            inst_12 arr_seq PState sched
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) prt
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         Bool_true
```
