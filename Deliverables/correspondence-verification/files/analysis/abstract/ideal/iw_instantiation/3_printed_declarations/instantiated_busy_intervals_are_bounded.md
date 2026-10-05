# `instantiated_busy_intervals_are_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_intervals_are_bounded`
- Certificate: `instantiated_busy_intervals_are_bounded_correspondence`

## Official Rocq

```coq
instantiated_busy_intervals_are_bounded :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (tsk : Equality.sort Task) {JobReady0 : @JobReady Job (ideal.processor_state Job) H2 H1},
@work_bearing_readiness Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched JLFP ->
@work_conserving.work_conserving Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched ->
forall {H3 : MaxArrivals Task} (ts : seq (Equality.sort Task)),
@taskset_respects_max_arrivals Task Job H0 arr_seq H3 ts ->
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H3 ts L ->
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
@busy_intervals_are_bounded_by Job Task H0 H1 H2 (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_jlfp_interference Job arr_seq sched JLFP)
  (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) L

instantiated_busy_intervals_are_bounded is not universe polymorphic
Arguments instantiated_busy_intervals_are_bounded {Task H Job H0 H1 H2} arr_seq H_valid_arrival_sequence
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_priority_is_reflexive tsk {JobReady0} H_work_bearing_readiness H_work_conserving 
  {H3} ts%seq_scope H_taskset_respects_max_arrivals H_all_jobs_from_taskset L H_L_positive 
  H_fixed_point H_arrivals_have_valid_job_costs j _ _ _
instantiated_busy_intervals_are_bounded is opaque
Expands to: Constant prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 654, characters 12-51
@instantiated_busy_intervals_are_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (tsk : Equality.sort Task) (JobReady0 : @JobReady Job (ideal.processor_state Job) H2 H1),
       @work_bearing_readiness Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched JLFP ->
       @work_conserving.work_conserving Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched ->
       forall (H3 : MaxArrivals Task) (ts : seq (Equality.sort Task)),
       @taskset_respects_max_arrivals Task Job H0 arr_seq H3 ts ->
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H3 ts L ->
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       @busy_intervals_are_bounded_by Job Task H0 H1 H2 (ideal.processor_state Job) arr_seq sched tsk
         (@ideal_jlfp_interference Job arr_seq sched JLFP)
         (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) L
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_intervals_are_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
              Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                ∀ (tsk : Task)
                  [JobReady0 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      ∀ [inst_6 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task),
                        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                          Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                            ∀ (L : Prosa.Behavior.Time.duration),
                              0 < L →
                                L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
                                  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                                    Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk
                                      L
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_busy_intervals_are_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_17 arr_seq ->
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
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_20 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall (tsk : Task)
         (JobReady0 : Prosa_Behavior_Ready_JobReady_inst4 Job
                        inst_7
                        (Prosa_Model_Processor_Ideal_processor_state Job
                           inst_7)
                        inst_20
                        inst_17),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4 Job
         inst_7
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         JobReady0 arr_seq sched JLFP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         JobReady0 arr_seq sched ->
       forall
         (inst_73 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_13 arr_seq
         inst_73 ts ->
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_13 arr_seq ts ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_73 ts L) ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_13
         inst_20 arr_seq ->
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            JLFP)
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_20 arr_seq sched
            JLFP)
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched Task
         inst_3
         inst_13 tsk L
```
