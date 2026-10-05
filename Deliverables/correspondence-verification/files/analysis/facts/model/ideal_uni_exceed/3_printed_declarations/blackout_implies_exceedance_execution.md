# `blackout_implies_exceedance_execution`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal_uni_exceed.blackout_implies_exceedance_execution`
- Lean: `Prosa.Analysis.Facts.Model.IdealUniExceed.blackout_implies_exceedance_execution`
- Certificate: `facts_blackout_statement_correspondence`

## Official Rocq

```coq
blackout_implies_exceedance_execution :
forall {Job : JobType} (sched : @schedule Job (ideal_uni_exceed.exceedance_proc_state Job)) (t : instant),
@is_blackout Job (ideal_uni_exceed.exceedance_proc_state Job) sched t = @is_exceedance_exec Job (sched t)

blackout_implies_exceedance_execution is not universe polymorphic
Arguments blackout_implies_exceedance_execution {Job} sched t
blackout_implies_exceedance_execution is opaque
Expands to: Constant prosa.analysis.facts.model.ideal_uni_exceed.blackout_implies_exceedance_execution
Declared in library prosa.analysis.facts.model.ideal_uni_exceed, line 102, characters 8-45
@blackout_implies_exceedance_execution
     : forall (Job : JobType) (sched : @schedule Job (ideal_uni_exceed.exceedance_proc_state Job))
         (t : instant),
       @is_blackout Job (ideal_uni_exceed.exceedance_proc_state Job) sched t =
       @is_exceedance_exec Job (sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.IdealUniExceed.blackout_implies_exceedance_execution : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Supply.is_blackout sched t =
    Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec (sched t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_blackout_implies_exceedance_execution
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_is_blackout_inst4 Job
            inst_3
            (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
               inst_3)
            sched t)
         (Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job
            inst_3 
            (sched t))
```
