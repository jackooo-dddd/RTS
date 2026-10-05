# `scheduled_at_procstate`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal_uni_exceed.scheduled_at_procstate`
- Lean: `Prosa.Analysis.Facts.Model.IdealUniExceed.scheduled_at_procstate`
- Certificate: `facts_scheduled_at_procstate_statement_correspondence`

## Official Rocq

```coq
scheduled_at_procstate :
forall {Job : JobType} (sched : @schedule Job (ideal_uni_exceed.exceedance_proc_state Job))
  (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job (ideal_uni_exceed.exceedance_proc_state Job) sched j t) <->
sched t = @ideal_uni_exceed.NominalExecution Job j \/ sched t = @ideal_uni_exceed.ExceedanceExecution Job j

scheduled_at_procstate is not universe polymorphic
Arguments scheduled_at_procstate {Job} sched j t
scheduled_at_procstate is opaque
Expands to: Constant prosa.analysis.facts.model.ideal_uni_exceed.scheduled_at_procstate
Declared in library prosa.analysis.facts.model.ideal_uni_exceed, line 27, characters 8-30
@scheduled_at_procstate
     : forall (Job : JobType) (sched : @schedule Job (ideal_uni_exceed.exceedance_proc_state Job))
         (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job (ideal_uni_exceed.exceedance_proc_state Job) sched j t) <->
       sched t = @ideal_uni_exceed.NominalExecution Job j \/
       sched t = @ideal_uni_exceed.ExceedanceExecution Job j
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.IdealUniExceed.scheduled_at_procstate : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job)) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at sched j t = true ↔
    sched t = Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.NominalExecution j ∨
      sched t = Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_scheduled_at_procstate
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                       inst_3))
         (j : Job) (t : Prosa_Behavior_Time_instant),
       Iff
         (@eq Bool
            (Prosa_Behavior_Service_scheduled_at_inst4 Job
               inst_3
               (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                  inst_3)
               sched j t)
            Bool_true)
         (Or
            (@eq
               (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                     inst_3))
               (sched t)
               (Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution Job j))
            (@eq
               (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                     inst_3))
               (sched t)
               (Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution Job j)))
```
