# `cumulative_hep_interference_split_tasks_new`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new`
- Lean: `Prosa.Analysis.Facts.Interference.cumulative_hep_interference_split_tasks_new`
- Certificate: `cumulative_hep_interference_split_tasks_new_correspondence`

## Official Rocq

```coq
cumulative_hep_interference_split_tasks_new :
forall {Task : TaskType} {Job : JobType} {jt : JobTask Job Task} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {FP : FP_policy Task}
  {JLFP : JLFP_policy Job},
@JLFP_FP_compatible Task Job jt JLFP FP ->
@uniprocessor_model Job PState ->
forall (j : Equality.sort Job) (t1 : instant) (Δ : nat),
@cumulative_another_task_hep_job_interference Task Job jt PState arr_seq sched JLFP j t1 (t1 + Δ) =
@cumulative_interference_from_hep_jobs_from_hp_tasks Task Job jt PState arr_seq sched FP JLFP j t1 (t1 + Δ) +
@cumulative_interference_from_hep_jobs_from_other_ep_tasks Task Job jt PState arr_seq sched FP JLFP j t1
  (t1 + Δ)

cumulative_hep_interference_split_tasks_new is not universe polymorphic
Arguments cumulative_hep_interference_split_tasks_new {Task Job jt PState} arr_seq 
  sched {FP JLFP} H_compatible H_uniproc j t1 Δ%nat_scope
cumulative_hep_interference_split_tasks_new is opaque
Expands to: Constant prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new
Declared in library prosa.analysis.facts.interference, line 75, characters 8-51
@cumulative_hep_interference_split_tasks_new
     : forall (Task : TaskType) (Job : JobType) (jt : JobTask Job Task) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (FP : FP_policy Task)
         (JLFP : JLFP_policy Job),
       @JLFP_FP_compatible Task Job jt JLFP FP ->
       @uniprocessor_model Job PState ->
       forall (j : Equality.sort Job) (t1 : instant) (Δ : nat),
       @cumulative_another_task_hep_job_interference Task Job jt PState arr_seq sched JLFP j t1 (t1 + Δ) =
       @cumulative_interference_from_hep_jobs_from_hp_tasks Task Job jt PState arr_seq sched FP JLFP j t1
         (t1 + Δ) +
       @cumulative_interference_from_hep_jobs_from_other_ep_tasks Task Job jt PState arr_seq sched FP JLFP j
         t1 (t1 + Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.cumulative_hep_interference_split_tasks_new : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible JLFP FP →
    Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
      ∀ (j : Job) (t1 : Prosa.Behavior.Time.instant) (Δ : ℕ),
        Prosa.Analysis.Definitions.Interference.cumulative_another_task_hep_job_interference arr_seq sched j t1
            (t1 + Δ) =
          Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_hp_tasks arr_seq sched j t1
              (t1 + Δ) +
            Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks arr_seq
              sched j t1 (t1 + Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_cumulative_hep_interference_split_tasks_new
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
         inst_3 Job
         inst_7
         inst_10 JLFP FP ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       forall (j : Job) (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Nat),
       @eq Nat
         (Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq sched JLFP
            j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
               (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_hp_tasks Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq sched
               FP JLFP j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_))
            (Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks
               Task inst_3 Job
               inst_7
               inst_10 PState arr_seq sched
               FP JLFP j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                  (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)))
```
