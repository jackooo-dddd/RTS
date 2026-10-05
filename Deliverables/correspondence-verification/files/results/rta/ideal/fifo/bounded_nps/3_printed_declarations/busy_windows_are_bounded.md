# `busy_windows_are_bounded`

- Kind (Rocq): Fact
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.busy_windows_are_bounded`
- Certificate: `busy_windows_are_bounded_correspondence`

## Official Rocq

```coq
busy_windows_are_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
forall (tsk : Equality.sort Task) (sched : @schedule Job (ideal.processor_state Job)),
@valid_schedule Job H3 (ideal.processor_state Job) sched H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
@work_conserving.work_conserving Job H3 H4 (ideal.processor_state Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H0 ts L ->
       (@ideal_jlfp_interference Job H3 arr_seq sched)
       (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched)]
  L

busy_windows_are_bounded is not universe polymorphic
Arguments busy_windows_are_bounded {Task H H0 Job H2 H3 H4} arr_seq H_valid_arrival_sequence 
  H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve tsk sched 
  H_valid_schedule H_work_conserving L H_L_positive H_fixed_point j _ _ _
busy_windows_are_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 203, characters 7-31
@busy_windows_are_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
       forall (tsk : Equality.sort Task) (sched : @schedule Job (ideal.processor_state Job)),
       @valid_schedule Job H3 (ideal.processor_state Job) sched H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
       @work_conserving.work_conserving Job H3 H4 (ideal.processor_state Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H0 ts L ->
       @busy_intervals_are_bounded_by Job Task H2 H3 H4 (ideal.processor_state Job) arr_seq sched tsk
         (@ideal_jlfp_interference Job H3 arr_seq sched)
         (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched) L
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.busy_windows_are_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : List Task),
        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
            ∀ (tsk : Task) (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
              Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                  ∀ (L : Prosa.Behavior.Time.duration),
                    0 < L →
                      L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
                        Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_busy_windows_are_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq
         inst_13 ts ->
       forall (tsk : Task)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7)),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_23
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_20
            inst_23)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_20
            inst_23)
         arr_seq sched ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_13 ts L) ->
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_20))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_23 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_20))
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched Task inst_3
         inst_16 tsk L
```
