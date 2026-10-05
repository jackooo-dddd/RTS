# `instantiated_task_interference_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedPi.instantiated_task_interference_is_bounded`
- Certificate: `instantiated_task_interference_is_bounded_correspondence`

## Official Rocq

```coq
instantiated_task_interference_is_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {Job : JobType} 
  {H3 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
@arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H3 arr_seq ts ->
forall {H5 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H3 arr_seq H5 ts ->
forall (tsk : Equality.sort Task) (priority_inversion_bound : duration -> duration),
@priority_inversion_is_bounded_by Task Job H3 Arrival Cost (ideal.processor_state Job) arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H3)) tsk priority_inversion_bound ->
@task_interference_is_bounded_by Job Task H3 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_jlfp_interference Task H0 Job H3 Arrival arr_seq sched)
  (@ideal_jlfp_interfering_workload Task H0 Job H3 Arrival Cost arr_seq sched)
  (fun A R : duration => priority_inversion_bound A + @bound_on_athep_workload Task H H0 H5 ts tsk A R)

instantiated_task_interference_is_bounded is not universe polymorphic
Arguments instantiated_task_interference_is_bounded {Task H H0 Job H3 Arrival Cost} 
  arr_seq H_valid_arrival_sequence sched H_sched_valid H_valid_job_cost ts%seq_scope 
  H_all_jobs_from_taskset {H5} H_is_arrival_curve tsk priority_inversion_bound%function_scope
  H_priority_inversion_is_bounded t1 t2 Δ j _ _ _ _ _ X _
instantiated_task_interference_is_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded
Declared in library prosa.results.rta.ideal.edf.bounded_pi, line 227, characters 8-49
@instantiated_task_interference_is_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (Job : JobType)
         (H3 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H3 arr_seq ts ->
       forall H5 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H3 arr_seq H5 ts ->
       forall (tsk : Equality.sort Task) (priority_inversion_bound : duration -> duration),
       @priority_inversion_is_bounded_by Task Job H3 Arrival Cost (ideal.processor_state Job) arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H3)) tsk priority_inversion_bound ->
       @task_interference_is_bounded_by Job Task H3 Arrival Cost (ideal.processor_state Job) arr_seq sched
         tsk (@ideal_jlfp_interference Task H0 Job H3 Arrival arr_seq sched)
         (@ideal_jlfp_interfering_workload Task H0 Job H3 Arrival Cost arr_seq sched)
         (fun A R : duration => priority_inversion_bound A + @bound_on_athep_workload Task H H0 H5 ts tsk A R)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedPi.instantiated_task_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
          ∀ (ts : List Task),
            Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
              ∀ [inst_7 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                  ∀ (tsk : Task)
                    (priority_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                    Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq sched tsk
                        priority_inversion_bound →
                      Prosa.Analysis.Abstract.IBF.Task.task_interference_is_bounded_by arr_seq sched tsk fun A R =>
                        priority_inversion_bound A +
                          Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedPi_instantiated_task_interference_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
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
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
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
       forall
         inst_66 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq
         inst_66 ts ->
       forall (tsk : Task)
         (priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_7
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_7
               inst_3
               inst_13
               inst_20
               inst_16))
         tsk priority_inversion_bound ->
       Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by_inst8 Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched tsk
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Edf_EDF Job
               inst_7
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_7
                  inst_3
                  inst_13
                  inst_20
                  inst_16)))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_23 arr_seq sched
            (Prosa_Model_Priority_Edf_EDF Job
               inst_7
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_7
                  inst_3
                  inst_13
                  inst_20
                  inst_16)))
         (fun A R : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A)
            (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
               inst_3
               inst_10
               inst_13
               inst_66 ts tsk A R))
```
