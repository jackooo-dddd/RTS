# `schedule_changes_bounded_by_total_arrivals_FP`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_FP`
- Certificate: `schedule_changes_bounded_by_total_arrivals_FP_correspondence`

## Official Rocq

```coq
schedule_changes_bounded_by_total_arrivals_FP :
forall {Task : TaskType} {H : MaxArrivals Task} {FP : FP_policy Task} {Job : JobType} 
  {H0 : JobArrival Job} {H1 : JobTask Job Task} {H2 : JobCost Job} {H3 : JobPreemptable Job},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H0 arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H0 (processor_state Job) sched H2 (@basic_ready_instance Job (processor_state Job) H0 H2)
  arr_seq ->
@work_conserving Job H0 H2 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H0 H2)
  arr_seq sched ->
@no_superfluous_preemptions Job H2 (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H1 FP)) 
  (processor_state Job) sched ->
@respects_FP_policy_at_preemption_point Task Job H1 H0 H2 (processor_state Job) H3
  (@basic_ready_instance Job (processor_state Job) H0 H2) arr_seq sched FP ->
@valid_preemption_model Job H2 H3 (processor_state Job) arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H0 H2 (processor_state Job) arr_seq sched (@FP_to_JLFP Job Task H1 FP) j t1 t2 ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H ts ->
forall Δ : duration,
is_true (t1 + Δ <= t2) ->
is_true
  (@number_schedule_changes Job sched t1.+1 (t1 + Δ) <=
   2 * (\sum_(tsk <- ts | @hep_task Task FP tsk (@job_task Job Task H1 j)) @max_arrivals Task H tsk Δ))

schedule_changes_bounded_by_total_arrivals_FP is not universe polymorphic
Arguments schedule_changes_bounded_by_total_arrivals_FP {Task H FP Job H0 H1 H2 H3} 
  H_priority_is_reflexive H_priority_is_transitive arr_seq H_valid_arrival_sequence 
  sched H_valid_schedule H_work_conserving H_no_superfluous_preemptions H_respects_policy
  H_valid_preemption_model j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix 
  ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve Δ H_subinterval
schedule_changes_bounded_by_total_arrivals_FP is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP
Declared in library prosa.analysis.facts.model.overheads.schedule_change_bound, line 568, characters 8-53
@schedule_changes_bounded_by_total_arrivals_FP
     : forall (Task : TaskType) (H : MaxArrivals Task) (FP : FP_policy Task) (Job : JobType)
         (H0 : JobArrival Job) (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobPreemptable Job),
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H0 arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H0 (processor_state Job) sched H2
         (@basic_ready_instance Job (processor_state Job) H0 H2) arr_seq ->
       @work_conserving Job H0 H2 (processor_state Job)
         (@basic_ready_instance Job (processor_state Job) H0 H2) arr_seq sched ->
       @no_superfluous_preemptions Job H2 (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H1 FP))
         (processor_state Job) sched ->
       @respects_FP_policy_at_preemption_point Task Job H1 H0 H2 (processor_state Job) H3
         (@basic_ready_instance Job (processor_state Job) H0 H2) arr_seq sched FP ->
       @valid_preemption_model Job H2 H3 (processor_state Job) arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H0 H2 (processor_state Job) arr_seq sched (@FP_to_JLFP Job Task H1 FP) j t1
         t2 ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H ts ->
       forall Δ : duration,
       is_true (t1 + Δ <= t2) ->
       is_true
         (@number_schedule_changes Job sched t1.+1 (t1 + Δ) <=
          2 * (\sum_(tsk <- ts | @hep_task Task FP tsk (@job_task Job Task H1 j)) @max_arrivals Task H tsk Δ))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_FP : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                  Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched FP →
                    Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                      ∀ (j : Job),
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                          Prosa.Model.Job.Properties.job_cost_positive j = true →
                            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                              Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
                                  t2 →
                                ∀ (ts : List Task),
                                  Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                                    Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                      ∀ (Δ : Prosa.Behavior.Time.duration),
                                        t1 + Δ ≤ t2 →
                                          Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes
                                              sched (t1 + 1) (t1 + Δ) ≤
                                            2 *
                                              Prosa.Util.Sum.sumFiltered ts
                                                (fun tsk =>
                                                  Prosa.Model.Priority.Definitions.hep_task tsk
                                                    (Prosa.Model.Task.Concept.job_task j))
                                                fun tsk => Prosa.Model.Task.Arrival.Curves.max_arrivals tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChangeBound_schedule_changes_bounded_by_total_arrivals_FP
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_12 : 
          DecidableEq Job)
         (inst_15 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_12)
         (inst_18 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_12
            Task
            inst_3)
         (inst_22 : 
          Prosa_Behavior_Job_JobCost Job
            inst_12)
         (inst_25 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_12),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_12,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_12
         inst_15
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_12
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_12),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_12
         inst_15
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_12)
         sched inst_22
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_12
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_12)
            inst_15
            inst_22)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_12
         inst_15
         inst_22
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_12)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_12
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_12)
            inst_15
            inst_22)
         arr_seq sched ->
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job
         inst_12
         inst_22
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_12
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_12
               Task
               inst_3
               inst_18
               FP))
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_12)
         sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst8 Task
         inst_3 Job
         inst_12
         inst_18
         inst_15
         inst_22
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_12)
         inst_25
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_12
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_12)
            inst_15
            inst_22)
         arr_seq sched FP ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_12
         inst_22
         inst_25
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_12)
         arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_12
         arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_12
            inst_22 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
         inst_12
         inst_15
         inst_22
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_12)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_12
            Task
            inst_3
            inst_18 FP)
         j t1 t2 ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_12
         inst_18
         arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_12
         inst_18
         arr_seq
         inst_6 ts ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_12
            sched
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat)
            (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))
            (Prosa_Util_Sum_sumFiltered Task ts
               (fun tsk : Task =>
                Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
                  inst_3
                  FP tsk
                  (Prosa_Model_Task_Concept_JobTask_job_task Job
                     inst_12
                     Task
                     inst_3
                     inst_18
                     j))
               (fun tsk : Task =>
                Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                  inst_3
                  inst_6
                  tsk _UU0394_)))
```
