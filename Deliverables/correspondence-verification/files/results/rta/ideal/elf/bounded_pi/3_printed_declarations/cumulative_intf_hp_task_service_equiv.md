# `cumulative_intf_hp_task_service_equiv`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.cumulative_intf_hp_task_service_equiv`
- Certificate: `cumulative_intf_hp_task_service_equiv_correspondence`

## Official Rocq

```coq
cumulative_intf_hp_task_service_equiv :
forall {Task : TaskType} {H3 : PriorityPoint Task} {Job : JobType} {H4 : JobTask Job Task}
  {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
  (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
forall FP : FP_policy Task,
@reflexive_task_priorities Task FP ->
forall j : Equality.sort Job,
is_true (@job_cost_positive Job Cost j) ->
@arrives_in Job arr_seq j ->
forall t1 t2 : instant,
@busy_interval Job Arrival Cost (ideal.processor_state Job) sched
  (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
  (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP) j t1 t2 ->
forall Δ : duration,
@cumulative_interference_from_hep_jobs_from_hp_tasks Task Job H4 (ideal.processor_state Job) arr_seq sched FP
  (@ELF Task H3 Job Arrival H4 FP) j t1 (t1 + Δ) =
@service_of_hp_jobs_from_other_hp_tasks Task H3 Job H4 Arrival arr_seq sched FP j t1 (t1 + Δ)

cumulative_intf_hp_task_service_equiv is not universe polymorphic
Arguments cumulative_intf_hp_task_service_equiv {Task H3 Job H4 Arrival Cost} arr_seq
  H_valid_arrival_sequence sched H_sched_valid FP H_reflexive_priorities j H_job_cost_positive 
  H_j_in_arr_seq t1 t2 H_busy_window Δ
cumulative_intf_hp_task_service_equiv is opaque
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 383, characters 10-47
@cumulative_intf_hp_task_service_equiv
     : forall (Task : TaskType) (H3 : PriorityPoint Task) (Job : JobType) (H4 : JobTask Job Task)
         (Arrival : JobArrival Job) (Cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
         (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       forall j : Equality.sort Job,
       is_true (@job_cost_positive Job Cost j) ->
       @arrives_in Job arr_seq j ->
       forall t1 t2 : instant,
       @busy_interval Job Arrival Cost (ideal.processor_state Job) sched
         (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
         (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP) j t1 t2 ->
       forall Δ : duration,
       @cumulative_interference_from_hep_jobs_from_hp_tasks Task Job H4 (ideal.processor_state Job) arr_seq
         sched FP (@ELF Task H3 Job Arrival H4 FP) j t1 (t1 + Δ) =
       @service_of_hp_jobs_from_other_hp_tasks Task H3 Job H4 Arrival arr_seq sched FP j t1 (t1 + Δ)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.cumulative_intf_hp_task_service_equiv : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
          Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
            ∀ (j : Job),
              Prosa.Model.Job.Properties.job_cost_positive j = true →
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                    Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                      ∀ (Δ : Prosa.Behavior.Time.duration),
                        Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_hp_tasks
                            arr_seq sched j t1 (t1 + Δ) =
                          Prosa.Results.Rta.Ideal.Elf.BoundedPi.service_of_hp_jobs_from_other_hp_tasks arr_seq sched FP
                            j t1 (t1 + Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_cumulative_intf_hp_task_service_equiv
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
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
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_20
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_17
            inst_20)
         arr_seq ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_20 j)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_10 Job
               inst_7
               inst_17
               inst_13 FP))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_20 arr_seq sched
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_10 Job
               inst_7
               inst_17
               inst_13 FP))
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       @eq Nat
         (Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_hp_tasks_inst8
            Task inst_3 Job
            inst_7
            inst_13
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            arr_seq sched FP
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_10 Job
               inst_7
               inst_17
               inst_13 FP)
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (Prosa_Results_Rta_Ideal_Elf_BoundedPi_service_of_hp_jobs_from_other_hp_tasks Task
            inst_3 Job
            inst_7
            inst_10
            inst_13
            inst_17 arr_seq sched FP j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
```
