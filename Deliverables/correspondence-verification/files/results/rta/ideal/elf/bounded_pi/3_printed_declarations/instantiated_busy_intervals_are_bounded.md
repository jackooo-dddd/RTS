# `instantiated_busy_intervals_are_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.instantiated_busy_intervals_are_bounded`
- Certificate: `instantiated_busy_intervals_are_bounded_correspondence`

## Official Rocq

```coq
instantiated_busy_intervals_are_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {H3 : PriorityPoint Task}
  {Job : JobType} {H4 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job}
  {H5 : JobPreemptable Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
@arrivals_have_valid_job_costs Task H Job H4 Cost arr_seq ->
forall ts : seq (Equality.sort Task),
is_true (@uniq Task ts) ->
@all_jobs_from_taskset Task Job H4 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H4 arr_seq H2 ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job (ideal.processor_state Job),
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
@work_conserving.work_conserving Job Arrival Cost (ideal.processor_state Job)
  (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched ->
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
(forall (j : Equality.sort Job) (t1 : nat),
 @job_task Job Task H4 j = tsk ->
 is_true
   (priority_inversion_ep_tasks_bound (@job_arrival Job Arrival j - t1) <=
    \max_(i <- ts | (fun (tsk_other : Equality.sort Task) (j0 : Equality.sort Job) (t2 : instant) =>
                     @ep_task Task FP tsk_other tsk &&
                     ~~
                     (fun (j1 : Equality.sort Job) (t3 : instant) (tsk_other0 : Equality.sort Task) =>
                      (0 <=
                       ...%:R - t3%:R + @task_priority_point Task H3 tsk -
                       @task_priority_point Task H3 tsk_other0)%R) j0 t2 tsk_other &&
                     (fun tsk_o : Equality.sort Task =>
                      (0 < @max_arrivals Task H2 tsk_o 1) && (0 < @task_cost Task H tsk_o)) tsk_other) i j t1)
       @task_cost Task H i)) ->
forall L : duration,
is_true (0 < L) ->
L = priority_inversion_lp_tasks_bound + @total_hep_request_bound_function_FP Task H H2 ts FP tsk L ->
@busy_intervals_are_bounded_by Job Task H4 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
  (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP) L

instantiated_busy_intervals_are_bounded is not universe polymorphic
Arguments instantiated_busy_intervals_are_bounded {Task H H2 H3 Job H4 Arrival Cost H5} 
  arr_seq H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_task_set H_all_jobs_from_taskset
  H_is_arrival_curve H_valid_arrival_curve tsk H_tsk_in_ts sched H_sched_valid FP 
  H_reflexive_priorities H_transitive_priorities H_total_priorities H_valid_preemption_model
  H_respects_policy H_work_conserving priority_inversion_lp_tasks_bound
  H_priority_inversion_from_lp_tasks_is_bounded priority_inversion_ep_tasks_bound%function_scope
  H_priority_inversion_from_ep_tasks_is_bounded
  H_priority_inversion_from_ep_tasks_concrete_bound%function_scope L H_L_positive 
  H_fixed_point j _ _ _
instantiated_busy_intervals_are_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 257, characters 8-47
@instantiated_busy_intervals_are_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (H3 : PriorityPoint Task)
         (Job : JobType) (H4 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H5 : JobPreemptable Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H4 Cost arr_seq ->
       forall ts : seq (Equality.sort Task),
       is_true (@uniq Task ts) ->
       @all_jobs_from_taskset Task Job H4 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H4 arr_seq H2 ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job (ideal.processor_state Job),
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
       @work_conserving.work_conserving Job Arrival Cost (ideal.processor_state Job)
         (@basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched ->
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
       (forall (j : Equality.sort Job) (t1 : nat),
        @job_task Job Task H4 j = tsk ->
        is_true
          (priority_inversion_ep_tasks_bound (@job_arrival Job Arrival j - t1) <=
           \max_(i <- ts | [&& @ep_task Task FP i tsk &&
                               ~~
                               (0 <=
                                (@job_arrival Job Arrival j)%:R - t1%:R + @task_priority_point Task H3 tsk -
                                @task_priority_point Task H3 i)%R,
                               0 < @max_arrivals Task H2 i 1
                             & 0 < @task_cost Task H i])
              @task_cost Task H i)) ->
       forall L : duration,
       is_true (0 < L) ->
       L = priority_inversion_lp_tasks_bound + @total_hep_request_bound_function_FP Task H H2 ts FP tsk L ->
       @busy_intervals_are_bounded_by Job Task H4 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
         (@ideal_elf_interference Task H3 Job H4 Arrival arr_seq sched FP)
         (@ideal_elf_interfering_workload Task H3 Job H4 Arrival Cost arr_seq sched FP) L
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.instantiated_busy_intervals_are_bounded : ∀
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
              Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                  Prosa.Model.Task.Arrival.Curves.max_arrivals →
                ∀ (tsk : Task),
                  decide (tsk ∈ ts) = true →
                    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
                      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                        ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
                          Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                            Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                              Prosa.Model.Priority.Definitions.total_task_priorities FP →
                                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                                  Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq
                                      sched (Prosa.Model.Priority.Elf.ELF FP) →
                                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
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
                                              (∀ (j : Job) (t1 : ℕ),
                                                  Prosa.Model.Task.Concept.job_task j = tsk →
                                                    priority_inversion_ep_tasks_bound
                                                        (Prosa.Behavior.Job.job_arrival j - t1) ≤
                                                      Prosa.Util.Sum.maxFiltered ts
                                                        (fun i =>
                                                          Prosa.Model.Priority.Definitions.ep_task i tsk &&
                                                              !decide
                                                                  (0 ≤
                                                                    ↑(Prosa.Behavior.Job.job_arrival j) - ↑t1 +
                                                                        Prosa.Model.Priority.Gel.task_priority_point
                                                                          tsk -
                                                                      Prosa.Model.Priority.Gel.task_priority_point i) &&
                                                            (decide
                                                                (0 <
                                                                  Prosa.Model.Task.Arrival.Curves.max_arrivals i 1) &&
                                                              decide (0 < Prosa.Model.Task.Concept.task_cost i)))
                                                        fun i => Prosa.Model.Task.Concept.task_cost i) →
                                                ∀ (L : Prosa.Behavior.Time.duration),
                                                  0 < L →
                                                    L =
                                                        priority_inversion_lp_tasks_bound +
                                                          Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                                            ts tsk L →
                                                      Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by
                                                        arr_seq sched tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_instantiated_busy_intervals_are_bounded
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
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13) ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
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
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_26)
         arr_seq sched ->
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
       (forall (j : Job) (t1 : Nat),
        @eq Task
          (Prosa_Model_Task_Concept_JobTask_job_task Job
             inst_7 Task
             inst_3
             inst_19 j)
          tsk ->
        LE_le_inst1 Prosa_Behavior_Time_duration instLENat
          (priority_inversion_ep_tasks_bound
             (HSub_hSub_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_7
                   inst_23 j)
                t1))
          (Prosa_Util_Sum_maxFiltered Task ts
             (fun i : Task =>
              Bool_and
                (Bool_and
                   (Prosa_Model_Priority_Definitions_ep_task Task
                      inst_3 FP i tsk)
                   (Bool_not
                      (Decidable_decide
                         (LE_le_inst1 Int Int_instLEInt (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                            (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                               (instHSub_inst1 Int Int_instSub)
                               (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                  (instHAdd_inst1 Int Int_instAdd) (HSub_hSub_inst7 Int Int Int ... ... ...)
                                  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                     inst_3
                                     inst_16
                                     tsk))
                               (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                  inst_3
                                  inst_16
                                  i)))
                         (Int_decLe (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                            (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                               (instHSub_inst1 Int Int_instSub)
                               (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                  (instHAdd_inst1 Int Int_instAdd) (HSub_hSub_inst7 Int Int Int ... ... ...)
                                  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                     inst_3
                                     inst_16
                                     tsk))
                               (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                  inst_3
                                  inst_16
                                  i))))))
                (Bool_and
                   (Decidable_decide
                      (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                            inst_3
                            inst_13 i
                            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                      (Nat_decLt (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
                         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                            inst_3
                            inst_13 i
                            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
                   (Decidable_decide
                      (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
                         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                            inst_3
                            inst_10 i))
                      (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
                         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                            inst_3
                            inst_10 i)))))
             (fun i : Task =>
              Prosa_Model_Task_Concept_TaskCost_task_cost Task
                inst_3
                inst_10 i))) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_lp_tasks_bound
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_10
               inst_13 ts FP tsk L)) ->
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by_inst4 Job
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
         arr_seq sched Task inst_3
         inst_19 tsk L
```
