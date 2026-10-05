# `schedule_changes_bounded_by_total_arrivals_FIFO`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_FIFO`
- Certificate: `schedule_changes_bounded_by_total_arrivals_FIFO_correspondence`

## Official Rocq

```coq
schedule_changes_bounded_by_total_arrivals_FIFO :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobPreemptable Job}
  {JLFP : JLFP_policy Job},
@policy_is_FIFO Job H JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H (processor_state Job) sched H0 (@basic_ready_instance Job (processor_state Job) H H0)
  arr_seq ->
@work_conserving Job H H0 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H H0)
  arr_seq sched ->
@no_superfluous_preemptions Job H0 (@JLFP_to_JLDP Job JLFP) (processor_state Job) sched ->
@respects_JLFP_policy_at_preemption_point Job H H0 (processor_state Job) H1
  (@basic_ready_instance Job (processor_state Job) H H0) arr_seq sched JLFP ->
@valid_preemption_model Job H0 H1 (processor_state Job) arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H0 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H H0 (processor_state Job) arr_seq sched JLFP j t1 t2 ->
forall {Task : TaskType} {H2 : MaxArrivals Task} {H3 : JobTask Job Task} (ts : seq (Equality.sort Task)),
@all_jobs_from_taskset Task Job H3 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H3 arr_seq H2 ts ->
forall Δ : duration,
is_true (t1 + Δ <= t2) ->
is_true (@number_schedule_changes Job sched t1.+1 (t1 + Δ) <= \sum_(tsk <- ts) @max_arrivals Task H2 tsk Δ)

schedule_changes_bounded_by_total_arrivals_FIFO is not universe polymorphic
Arguments schedule_changes_bounded_by_total_arrivals_FIFO {Job H H0 H1 JLFP} H_FIFO 
  arr_seq H_valid_arrival_sequence sched H_valid_schedule H_work_conserving H_no_superfluous_preemptions
  H_respects_policy H_valid_preemption_model j H_j_arrives H_job_cost_positive t1 
  t2 H_busy_interval_prefix {Task H2 H3} ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve 
  Δ H_subinterval
schedule_changes_bounded_by_total_arrivals_FIFO is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO
Declared in library prosa.analysis.facts.model.overheads.schedule_change_bound, line 659, characters 8-55
@schedule_changes_bounded_by_total_arrivals_FIFO
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobPreemptable Job)
         (JLFP : JLFP_policy Job),
       @policy_is_FIFO Job H JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H (processor_state Job) sched H0
         (@basic_ready_instance Job (processor_state Job) H H0) arr_seq ->
       @work_conserving Job H H0 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H H0)
         arr_seq sched ->
       @no_superfluous_preemptions Job H0 (@JLFP_to_JLDP Job JLFP) (processor_state Job) sched ->
       @respects_JLFP_policy_at_preemption_point Job H H0 (processor_state Job) H1
         (@basic_ready_instance Job (processor_state Job) H H0) arr_seq sched JLFP ->
       @valid_preemption_model Job H0 H1 (processor_state Job) arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H0 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H H0 (processor_state Job) arr_seq sched JLFP j t1 t2 ->
       forall (Task : TaskType) (H2 : MaxArrivals Task) (H3 : JobTask Job Task)
         (ts : seq (Equality.sort Task)),
       @all_jobs_from_taskset Task Job H3 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H3 arr_seq H2 ts ->
       forall Δ : duration,
       is_true (t1 + Δ <= t2) ->
       is_true
         (@number_schedule_changes Job sched t1.+1 (t1 + Δ) <= \sum_(tsk <- ts) @max_arrivals Task H2 tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_FIFO : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.policy_is_FIFO JLFP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
              Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                    ∀ (j : Job),
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                        Prosa.Model.Job.Properties.job_cost_positive j = true →
                          ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                            Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
                                t2 →
                              ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst_4 : DecidableEq Task]
                                [inst_5 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
                                [inst_6 : Prosa.Model.Task.Concept.JobTask Job Task] (ts : List Task),
                                Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                    ∀ (Δ : Prosa.Behavior.Time.duration),
                                      t1 + Δ ≤ t2 →
                                        Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes
                                            sched (t1 + 1) (t1 + Δ) ≤
                                          Prosa.Util.Sum.sumSeq ts fun tsk =>
                                            Prosa.Model.Task.Arrival.Curves.max_arrivals tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChangeBound_schedule_changes_bounded_by_total_arrivals_FIFO
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_policy_is_FIFO Job
         inst_3
         inst_6 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_3
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_3),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3
         inst_6
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         sched inst_9
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq sched ->
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job
         inst_3
         inst_9
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3 JLFP)
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         inst_12
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            inst_6
            inst_9)
         arr_seq sched JLFP ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq
         j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3)
         arr_seq sched JLFP j t1 t2 ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_117 : 
          DecidableEq Task)
         (inst_120 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_117)
         (inst_123 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_117)
         (ts : List Task),
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_117 Job
         inst_3
         inst_123
         arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_117 Job
         inst_3
         inst_123
         arr_seq
         inst_120 ts ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (Prosa_Util_Sum_sumSeq Task ts
            (fun tsk : Task =>
             Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
               inst_117
               inst_120
               tsk _UU0394_))
```
