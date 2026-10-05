# `idle_implies_no_priority_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.idle_implies_no_priority_inversion`
- Certificate: `idle_implies_no_priority_inversion_correspondence`

## Official Rocq

```coq
idle_implies_no_priority_inversion :
forall {Job : JobType} {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t : instant),
is_true (@ideal.ideal_is_idle Job sched t) ->
is_true (~~ @priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t)

idle_implies_no_priority_inversion is not universe polymorphic
Arguments idle_implies_no_priority_inversion {Job H1} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} j 
  t _
idle_implies_no_priority_inversion is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion
Declared in library prosa.analysis.facts.model.ideal.priority_inversion, line 54, characters 8-42
@idle_implies_no_priority_inversion
     : forall (Job : JobType) (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t : instant),
       is_true (@ideal.ideal_is_idle Job sched t) ->
       is_true (~~ @priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.idle_implies_no_priority_inversion : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j : Job) (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Processor.Ideal.ideal_is_idle sched t = true →
              (!Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_PriorityInversion_idle_implies_no_priority_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_3
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_3),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Ideal_ideal_is_idle Job
            inst_3 sched t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               arr_seq sched JLFP j t))
         Bool_true
```
