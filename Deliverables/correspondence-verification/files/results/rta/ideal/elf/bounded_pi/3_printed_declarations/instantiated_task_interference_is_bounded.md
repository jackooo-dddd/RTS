# `instantiated_task_interference_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.instantiated_task_interference_is_bounded`
- Certificate: `instantiated_task_interference_is_bounded_correspondence`

## Official Rocq

```coq
instantiated_task_interference_is_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {H3 : PriorityPoint Task}
  {Job : JobType} {H4 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job}
  {H5 : JobPreemptable Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
@arrivals_have_valid_job_costs Task H Job H4 Cost arr_seq ->
forall ts : seq (Equality.sort Task),
is_true (@uniq Task ts) ->
@all_jobs_from_taskset Task Job H4 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H4 arr_seq H2 ts ->
forall (tsk : Equality.sort Task) (sched : @schedule Job (ideal.processor_state Job)),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
  (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
forall FP : FP_policy Task,
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
@total_task_priorities Task FP ->
@valid_preemption_model Job Cost H5 (ideal.processor_state Job) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost (ideal.processor_state Job) H5
  (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched
  (@ELF Task H3 Job Arrival H4 FP) ->
forall priority_inversion_lp_tasks_bound : duration,
@priority_inversion_cond_is_bounded_by Task Job H4 Arrival Cost (ideal.processor_state Job) arr_seq sched
  (@ELF Task H3 Job Arrival H4 FP) tsk
  (fun j' : Equality.sort Job => @hp_task Task FP tsk (@job_task Job Task H4 j'))
  (@constant duration duration priority_inversion_lp_tasks_bound) ->
forall priority_inversion_ep_tasks_bound : duration -> duration,
@priority_inversion_cond_is_bounded_by Task Job H4 Arrival Cost (ideal.processor_state Job) arr_seq sched
  (@ELF Task H3 Job Arrival H4 FP) tsk
  (fun j' : Equality.sort Job => @ep_task Task FP tsk (@job_task Job Task H4 j'))
  priority_inversion_ep_tasks_bound ->
@task_interference_is_bounded_by Job Task H4 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
  (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP)
  (@task_IBF Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound)

instantiated_task_interference_is_bounded is not universe polymorphic
Arguments instantiated_task_interference_is_bounded {Task H H2 H3 Job H4 Arrival Cost H5} 
  arr_seq H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_task_set H_all_jobs_from_taskset
  H_is_arrival_curve tsk sched H_sched_valid FP H_reflexive_priorities H_transitive_priorities
  H_total_priorities H_valid_preemption_model H_respects_policy priority_inversion_lp_tasks_bound
  H_priority_inversion_from_lp_tasks_is_bounded priority_inversion_ep_tasks_bound%function_scope
  H_priority_inversion_from_ep_tasks_is_bounded t1 t2 Δ j _ _ _ _ _ X _
instantiated_task_interference_is_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 508, characters 8-49
@instantiated_task_interference_is_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (H3 : PriorityPoint Task)
         (Job : JobType) (H4 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H5 : JobPreemptable Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H4 Cost arr_seq ->
       forall ts : seq (Equality.sort Task),
       is_true (@uniq Task ts) ->
       @all_jobs_from_taskset Task Job H4 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H4 arr_seq H2 ts ->
       forall (tsk : Equality.sort Task) (sched : @schedule Job (ideal.processor_state Job)),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
         (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       @total_task_priorities Task FP ->
       @valid_preemption_model Job Cost H5 (ideal.processor_state Job) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost (ideal.processor_state Job) H5
         (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched
         (@ELF Task H3 Job Arrival H4 FP) ->
       forall priority_inversion_lp_tasks_bound : duration,
       @priority_inversion_cond_is_bounded_by Task Job H4 Arrival Cost (ideal.processor_state Job) arr_seq
         sched (@ELF Task H3 Job Arrival H4 FP) tsk
         (fun j' : Equality.sort Job => @hp_task Task FP tsk (@job_task Job Task H4 j'))
         (@constant duration duration priority_inversion_lp_tasks_bound) ->
       forall priority_inversion_ep_tasks_bound : duration -> duration,
       @priority_inversion_cond_is_bounded_by Task Job H4 Arrival Cost (ideal.processor_state Job) arr_seq
         sched (@ELF Task H3 Job Arrival H4 FP) tsk
         (fun j' : Equality.sort Job => @ep_task Task FP tsk (@job_task Job Task H4 j'))
         priority_inversion_ep_tasks_bound ->
       @task_interference_is_bounded_by Job Task H4 Arrival Cost (ideal.processor_state Job) arr_seq sched
         tsk (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
         (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP)
         (@task_IBF Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound
            priority_inversion_ep_tasks_bound)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.instantiated_task_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_4 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_6 : Prosa.Behavior.Job.JobArrival Job]
  [inst_7 : Prosa.Behavior.Job.JobCost Job] [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : List Task),
        ts.Nodup →
          Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
            Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
              ∀ (tsk : Task)
                (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
                Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                  ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
                    Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                      Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                        Prosa.Model.Priority.Definitions.total_task_priorities FP →
                          Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                            Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                                (Prosa.Model.Priority.Elf.ELF FP) →
                              ∀ (priority_inversion_lp_tasks_bound : Prosa.Behavior.Time.duration),
                                Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by
                                    arr_seq sched tsk
                                    (fun j' =>
                                      Prosa.Model.Priority.Definitions.hp_task tsk
                                        (Prosa.Model.Task.Concept.job_task j'))
                                    (Prosa.Util.Notation.constant priority_inversion_lp_tasks_bound) →
                                  ∀
                                    (priority_inversion_ep_tasks_bound :
                                      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                    Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by
                                        arr_seq sched tsk
                                        (fun j' =>
                                          Prosa.Model.Priority.Definitions.ep_task tsk
                                            (Prosa.Model.Task.Concept.job_task j'))
                                        priority_inversion_ep_tasks_bound →
                                      Prosa.Analysis.Abstract.IBF.Task.task_interference_is_bounded_by arr_seq sched tsk
                                        (Prosa.Results.Rta.Ideal.Elf.BoundedPi.task_IBF ts tsk FP
                                          priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_instantiated_task_interference_is_bounded
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
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_26 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_29 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_23 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_19
         inst_26 arr_seq ->
       forall ts : List Task,
       List_Nodup Task ts ->
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_19 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_19 arr_seq
         inst_13 ts ->
       forall (tsk : Task)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7)),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_26
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_26)
         arr_seq ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_26
         inst_29
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_7
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_29
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_26)
         arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_16 Job
            inst_7
            inst_23
            inst_19 FP) ->
       forall priority_inversion_lp_tasks_bound : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_19
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_16 Job
            inst_7
            inst_23
            inst_19 FP)
         tsk
         (fun j' : Job =>
          Prosa_Model_Priority_Definitions_hp_task Task
            inst_3 FP tsk
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_19 j'))
         (Prosa_Util_Notation_constant_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            priority_inversion_lp_tasks_bound) ->
       forall
         priority_inversion_ep_tasks_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_19
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_16 Job
            inst_7
            inst_23
            inst_19 FP)
         tsk
         (fun j' : Job =>
          Prosa_Model_Priority_Definitions_ep_task Task
            inst_3 FP tsk
            (Prosa_Model_Task_Concept_JobTask_job_task Job
               inst_7 Task
               inst_3
               inst_19 j'))
         priority_inversion_ep_tasks_bound ->
       Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by_inst8 Job
         inst_7 Task
         inst_3
         inst_19
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched tsk
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_16 Job
               inst_7
               inst_23
               inst_19 FP))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_26 arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_16 Job
               inst_7
               inst_23
               inst_19 FP))
         (Prosa_Results_Rta_Ideal_Elf_BoundedPi_task_IBF Task
            inst_3
            inst_10
            inst_13
            inst_16 ts tsk FP
            priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound)
```
