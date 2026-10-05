# `bound_on_ep_workload`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_ep_workload`
- Certificate: `bound_on_ep_workload_correspondence`

## Official Rocq

```coq
bound_on_ep_workload :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {H3 : PriorityPoint Task}
  {Job : JobType} {H4 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job}
  (arr_seq : arrival_sequence Job),
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
forall j : Equality.sort Job,
is_true (@job_of_task Job Task H4 tsk j) ->
is_true (@job_cost_positive Job Cost j) ->
@arrives_in Job arr_seq j ->
forall t1 t2 : instant,
@busy_interval Job Arrival Cost (ideal.processor_state Job) sched
  (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
  (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP) j t1 t2 ->
forall Δ : duration,
is_true (t1 + Δ <= t2) ->
is_true
  (@cumulative_interference_from_hep_jobs_from_other_ep_tasks Task Job H4 (ideal.processor_state Job) arr_seq
     sched FP (@ELF Task H3 Job Arrival H4 FP) j t1 (t1 + Δ) <=
   @bound_on_total_ep_workload Task H H2 H3 ts tsk FP (@job_arrival Job Arrival j - t1) Δ)

bound_on_ep_workload is not universe polymorphic
Arguments bound_on_ep_workload {Task H H2 H3 Job H4 Arrival Cost} arr_seq H_valid_arrival_sequence
  H_valid_job_cost ts%seq_scope H_task_set H_all_jobs_from_taskset H_is_arrival_curve 
  tsk sched H_sched_valid FP H_reflexive_priorities j H_job_of_task H_job_cost_positive 
  H_j_in_arr_seq t1 t2 H_busy_window Δ H_Δ_in_busy
bound_on_ep_workload is opaque
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 447, characters 10-30
@bound_on_ep_workload
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (H3 : PriorityPoint Task)
         (Job : JobType) (H4 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
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
       forall j : Equality.sort Job,
       is_true (@job_of_task Job Task H4 tsk j) ->
       is_true (@job_cost_positive Job Cost j) ->
       @arrives_in Job arr_seq j ->
       forall t1 t2 : instant,
       @busy_interval Job Arrival Cost (ideal.processor_state Job) sched
         (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
         (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP) j t1 t2 ->
       forall Δ : duration,
       is_true (t1 + Δ <= t2) ->
       is_true
         (@cumulative_interference_from_hep_jobs_from_other_ep_tasks Task Job H4 
            (ideal.processor_state Job) arr_seq sched FP (@ELF Task H3 Job Arrival H4 FP) j t1 
            (t1 + Δ) <=
          @bound_on_total_ep_workload Task H H2 H3 ts tsk FP (@job_arrival Job Arrival j - t1) Δ)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_ep_workload : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobArrival Job] [inst_7 : Prosa.Behavior.Job.JobCost Job]
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
                      ∀ (j : Job),
                        Prosa.Model.Task.Concept.job_of_task tsk j = true →
                          Prosa.Model.Job.Properties.job_cost_positive j = true →
                            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                                  ∀ (Δ : Prosa.Behavior.Time.duration),
                                    t1 + Δ ≤ t2 →
                                      Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks
                                          arr_seq sched j t1 (t1 + Δ) ≤
                                        Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload ts tsk FP
                                          (Prosa.Behavior.Job.job_arrival j - t1) Δ
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_ep_workload
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
       forall j : Job,
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_19 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_26 j)
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
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks_inst8
            Task inst_3 Job
            inst_7
            inst_19
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            arr_seq sched FP
            (Prosa_Model_Priority_Elf_ELF Task
               inst_3
               inst_16 Job
               inst_7
               inst_23
               inst_19 FP)
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload Task
            inst_3
            inst_10
            inst_13
            inst_16 ts tsk FP
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7
                  inst_23 j)
               t1)
            _UU0394_)
```
