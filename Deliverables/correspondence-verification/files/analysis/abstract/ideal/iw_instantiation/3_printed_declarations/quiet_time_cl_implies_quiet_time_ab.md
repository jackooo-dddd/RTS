# `quiet_time_cl_implies_quiet_time_ab`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.quiet_time_cl_implies_quiet_time_ab`
- Certificate: `quiet_time_cl_implies_quiet_time_ab_correspondence`

## Official Rocq

```coq
quiet_time_cl_implies_quiet_time_ab :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall t : instant,
@quiet_time Job H1 H2 (ideal.processor_state Job) arr_seq sched JLFP j t ->
is_true
  (@definitions.quiet_time Job H1 H2 (ideal.processor_state Job) sched
     (@ideal_jlfp_interference Job arr_seq sched JLFP)
     (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) j t)

quiet_time_cl_implies_quiet_time_ab is not universe polymorphic
Arguments quiet_time_cl_implies_quiet_time_ab {Job H1 H2} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_priority_is_reflexive j H_j_arrives t _
quiet_time_cl_implies_quiet_time_ab is opaque
Expands to: Constant prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 377, characters 10-45
@quiet_time_cl_implies_quiet_time_ab
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall t : instant,
       @quiet_time Job H1 H2 (ideal.processor_state Job) arr_seq sched JLFP j t ->
       is_true
         (@definitions.quiet_time Job H1 H2 (ideal.processor_state Job) sched
            (@ideal_jlfp_interference Job arr_seq sched JLFP)
            (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.quiet_time_cl_implies_quiet_time_ab : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
              Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                ∀ (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    ∀ (t : Prosa.Behavior.Time.instant),
                      Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t →
                        Prosa.Analysis.Abstract.Definitions.quiet_time sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_quiet_time_cl_implies_quiet_time_ab
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_7
         inst_10
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_13 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       forall t : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_inst4 Job
         inst_7
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched JLFP j t ->
       @eq Bool
         (Prosa_Analysis_Abstract_Definitions_quiet_time_inst4 Job
            inst_7
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
               inst_7 arr_seq
               sched JLFP)
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
               inst_7
               inst_13 arr_seq
               sched JLFP)
            inst_10
            inst_13
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            sched j t)
         Bool_true
```
