# `preemption_time_exists_case2`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.preemption_time_exists_case2`
- Certificate: `preemption_time_exists_case2_correspondence`

## Official Rocq

```coq
preemption_time_exists_case2 :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job} {H3 : TaskMaxNonpreemptiveSegment Task}
  {H4 : JobPreemptable Job} {JobReady0 : @JobReady Job PState H2 H1},
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
forall jhp : Equality.sort Job,
is_true (@scheduled_at Job PState sched jhp t1) ->
is_true (@hep_job Job JLFP jhp j) ->
exists pr_t : instant,
  is_true (@preemption_time Job H4 arr_seq PState sched pr_t) /\
  is_true (t1 <= pr_t <= t1 + @max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1)

preemption_time_exists_case2 is not universe polymorphic
Arguments preemption_time_exists_case2 {Task Job H0 H1 H2} arr_seq H_valid_arrivals 
  {PState} H_uni sched {JLFP H3 H4 JobReady0} H_sched_valid j t1 t2 H_busy_interval_prefix
  H_valid_model_with_bounded_nonpreemptive_segments jhp H_jhp_is_scheduled H_jhp_hep_priority
preemption_time_exists_case2 is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2
Declared in library prosa.analysis.facts.busy_interval.pi, line 429, characters 14-42
@preemption_time_exists_case2
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (H3 : TaskMaxNonpreemptiveSegment Task)
         (H4 : JobPreemptable Job) (JobReady0 : @JobReady Job PState H2 H1),
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
       forall jhp : Equality.sort Job,
       is_true (@scheduled_at Job PState sched jhp t1) ->
       is_true (@hep_job Job JLFP jhp j) ->
       exists pr_t : instant,
         is_true (@preemption_time Job H4 arr_seq PState sched pr_t) /\
         is_true (t1 <= pr_t <= t1 + @max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.preemption_time_exists_case2 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
          [inst_5 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
          [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
          [inst_7 : Prosa.Behavior.Ready.JobReady Job PState],
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
              Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
                  ∀ (jhp : Job),
                    Prosa.Behavior.Service.scheduled_at sched jhp t1 = true →
                      Prosa.Model.Priority.Definitions.hep_job jhp j = true →
                        ∃ pr_t,
                          Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched pr_t = true ∧
                            (decide (t1 ≤ pr_t) &&
                                decide
                                  (pr_t ≤
                                    t1 +
                                      Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment arr_seq j t1)) =
                              true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_exists_case2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_14 arr_seq ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_38 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_41 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (inst_44 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_17
            inst_14),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_14 PState sched
         inst_17
         inst_44 arr_seq ->
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_14
         inst_17 PState arr_seq sched JLFP
         j t1 t2 ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_10
         inst_17
         inst_38
         inst_41 PState arr_seq sched ->
       forall jhp : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jhp t1)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3 JLFP jhp j)
         Bool_true ->
       Exists Prosa_Behavior_Time_instant
         (fun pr_t : Prosa_Behavior_Time_instant =>
          And
            (@eq Bool
               (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                  inst_3
                  inst_41 arr_seq PState
                  sched pr_t)
               Bool_true)
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 pr_t)
                     (Nat_decLe t1 pr_t))
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat pr_t
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                           (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
                              inst_3
                              inst_17
                              arr_seq JLFP
                              inst_41 j t1)))
                     (Nat_decLe pr_t
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                           (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
                              inst_3
                              inst_17
                              arr_seq JLFP
                              inst_41 j t1)))))
               Bool_true))
```
