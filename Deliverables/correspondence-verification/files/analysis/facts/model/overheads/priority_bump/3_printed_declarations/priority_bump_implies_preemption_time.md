# `priority_bump_implies_preemption_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.PriorityBump.priority_bump_implies_preemption_time`
- Certificate: `priority_bump_implies_preemption_time_correspondence`

## Official Rocq

```coq
priority_bump_implies_preemption_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H (processor_state Job) sched H0 (@basic_ready_instance Job (processor_state Job) H H0)
  arr_seq ->
forall {H1 : JobPreemptable Job},
@valid_preemption_model Job H0 H1 (processor_state Job) arr_seq sched ->
forall t : instant,
is_true (@priority_bump Job JLFP sched t) ->
is_true (@preemption_time Job H1 arr_seq (processor_state Job) sched t)

priority_bump_implies_preemption_time is not universe polymorphic
Arguments priority_bump_implies_preemption_time {Job H H0 JLFP} H_priority_is_reflexive 
  arr_seq H_valid_arrival_sequence sched H_valid_schedule {H1} H_valid_preemption_model 
  t _
priority_bump_implies_preemption_time is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time
Declared in library prosa.analysis.facts.model.overheads.priority_bump, line 47, characters 8-45
@priority_bump_implies_preemption_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H (processor_state Job) sched H0
         (@basic_ready_instance Job (processor_state Job) H H0) arr_seq ->
       forall H1 : JobPreemptable Job,
       @valid_preemption_model Job H0 H1 (processor_state Job) arr_seq sched ->
       forall t : instant,
       is_true (@priority_bump Job JLFP sched t) ->
       is_true (@preemption_time Job H1 arr_seq (processor_state Job) sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.PriorityBump.priority_bump_implies_preemption_time : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                ∀ (t : Prosa.Behavior.Time.instant),
                  Prosa.Analysis.Definitions.Overheads.PriorityBump.priority_bump sched t = true →
                    Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_PriorityBump_priority_bump_implies_preemption_time
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
       forall
         inst_47 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_3
         inst_9
         inst_47
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         arr_seq sched ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump Job
            inst_3 JLFP sched
            t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time_inst4 Job
            inst_3
            inst_47 arr_seq
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            sched t)
         Bool_true
```
