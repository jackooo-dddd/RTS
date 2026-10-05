# `priority_inversion_equiv_sched_lower_priority`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.priority_inversion_equiv_sched_lower_priority`
- Certificate: `priority_inversion_equiv_sched_lower_priority_correspondence`

## Official Rocq

```coq
priority_inversion_equiv_sched_lower_priority :
forall {Job : JobType} {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (j : Equality.sort Job) (t : instant) (j' : Equality.sort Job),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j' t) ->
@priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t = ~~ @hep_job Job JLFP j' j

priority_inversion_equiv_sched_lower_priority is not universe polymorphic
Arguments priority_inversion_equiv_sched_lower_priority {Job H1} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive 
  j t j' H_j'_sched
priority_inversion_equiv_sched_lower_priority is opaque
Expands to: Constant
            prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority
Declared in library prosa.analysis.facts.model.ideal.priority_inversion, line 70, characters 8-53
@priority_inversion_equiv_sched_lower_priority
     : forall (Job : JobType) (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (j : Equality.sort Job) (t : instant) (j' : Equality.sort Job),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j' t) ->
       @priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t = ~~ @hep_job Job JLFP j' j
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.priority_inversion_equiv_sched_lower_priority : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
            Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
              ∀ (j : Job) (t : Prosa.Behavior.Time.instant) (j' : Job),
                Prosa.Behavior.Service.scheduled_at sched j' t = true →
                  Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq sched j t =
                    !Prosa.Model.Priority.Definitions.hep_job j' j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_PriorityInversion_priority_inversion_equiv_sched_lower_priority
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
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant) (j' : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j' t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            arr_seq sched JLFP j t)
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3 JLFP
               j' j))
```
