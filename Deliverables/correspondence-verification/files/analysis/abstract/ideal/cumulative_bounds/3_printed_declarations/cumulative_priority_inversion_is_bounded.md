# `cumulative_priority_inversion_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded`
- Lean: `Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_priority_inversion_is_bounded`
- Certificate: `cumulative_priority_inversion_is_bounded_correspondence`

## Official Rocq

```coq
cumulative_priority_inversion_is_bounded :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {JR : @JobReady Job (ideal.processor_state Job) H1 H0} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H0 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H0 (ideal.processor_state Job) sched H1 JR arr_seq ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H tsk j) ->
is_true (@job_cost_positive Job H1 j) ->
forall t1 t2 : duration,
@definitions.busy_interval Job H0 H1 (ideal.processor_state Job) sched
  (@ideal_jlfp_interference Job JLFP arr_seq sched)
  (@ideal_jlfp_interfering_workload Job H1 JLFP arr_seq sched) j t1 t2 ->
forall Δ : duration,
is_true (t1 + Δ <= t2) ->
forall priority_inversion_bound : duration -> duration,
@priority_inversion_is_bounded_by Task Job H H0 H1 (ideal.processor_state Job) arr_seq sched JLFP tsk
  priority_inversion_bound ->
is_true
  (@cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t1 (t1 + Δ) <=
   priority_inversion_bound (@job_arrival Job H0 j - t1))

cumulative_priority_inversion_is_bounded is not universe polymorphic
Arguments cumulative_priority_inversion_is_bounded {Task Job H H0 H1 JR JLFP} H_policy_is_reflexive 
  arr_seq H_valid_arrival_sequence sched H_valid_schedule tsk j H_j_arrives H_job_of_tsk 
  H_job_cost_positive t1 t2 H_busy_interval Δ H_Δ_in_busy priority_inversion_bound%function_scope
  H_priority_inversion_is_bounded
cumulative_priority_inversion_is_bounded is opaque
Expands to: Constant prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded
Declared in library prosa.analysis.abstract.ideal.cumulative_bounds, line 71, characters 10-50
@cumulative_priority_inversion_is_bounded
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (H1 : JobCost Job) (JR : @JobReady Job (ideal.processor_state Job) H1 H0) 
         (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H0 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H0 (ideal.processor_state Job) sched H1 JR arr_seq ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H tsk j) ->
       is_true (@job_cost_positive Job H1 j) ->
       forall t1 t2 : duration,
       @definitions.busy_interval Job H0 H1 (ideal.processor_state Job) sched
         (@ideal_jlfp_interference Job JLFP arr_seq sched)
         (@ideal_jlfp_interfering_workload Job H1 JLFP arr_seq sched) j t1 t2 ->
       forall Δ : duration,
       is_true (t1 + Δ <= t2) ->
       forall priority_inversion_bound : duration -> duration,
       @priority_inversion_is_bounded_by Task Job H H0 H1 (ideal.processor_state Job) arr_seq sched JLFP tsk
         priority_inversion_bound ->
       is_true
         (@cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t1 (t1 + Δ) <=
          priority_inversion_bound (@job_arrival Job H0 j - t1))
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_priority_inversion_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  [JR : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ (tsk : Task) (j : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                Prosa.Model.Task.Concept.job_of_task tsk j = true →
                  Prosa.Model.Job.Properties.job_cost_positive j = true →
                    ∀ (t1 t2 : Prosa.Behavior.Time.duration),
                      Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                        ∀ (Δ : Prosa.Behavior.Time.duration),
                          t1 + Δ ≤ t2 →
                            ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                              Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq
                                  sched tsk priority_inversion_bound →
                                Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched
                                    j t1 (t1 + Δ) ≤
                                  priority_inversion_bound (Prosa.Behavior.Job.job_arrival j - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_CumulativeBounds_cumulative_priority_inversion_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (JR : Prosa_Behavior_Ready_JobReady_inst4 Job
                 inst_7
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_7)
                 inst_17
                 inst_14)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_14
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_17 JR
         arr_seq ->
       forall (tsk : Task) (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_interval_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            JLFP)
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_17 arr_seq
            sched JLFP)
         inst_14
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1 _UU0394_)
         t2 ->
       forall priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_10
         inst_14
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched JLFP tsk priority_inversion_bound ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            arr_seq sched JLFP j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
               _UU0394_))
         (priority_inversion_bound
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7
                  inst_14 j)
               t1))
```
