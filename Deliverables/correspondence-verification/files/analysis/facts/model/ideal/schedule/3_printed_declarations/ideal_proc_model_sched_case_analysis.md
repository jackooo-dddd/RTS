# `ideal_proc_model_sched_case_analysis`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_sched_case_analysis`
- Certificate: `ideal_proc_model_sched_case_analysis_correspondence`

## Official Rocq

```coq
ideal_proc_model_sched_case_analysis :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (t : instant),
is_true (@ideal.ideal_is_idle Job sched t) \/
(exists j : Equality.sort Job, is_true (@scheduled_at Job (ideal.processor_state Job) sched j t))

ideal_proc_model_sched_case_analysis is not universe polymorphic
Arguments ideal_proc_model_sched_case_analysis {Job} sched t
ideal_proc_model_sched_case_analysis is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis
Declared in library prosa.analysis.facts.model.ideal.schedule, line 146, characters 8-44
@ideal_proc_model_sched_case_analysis
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) (t : instant),
       is_true (@ideal.ideal_is_idle Job sched t) \/
       (exists j : Equality.sort Job, is_true (@scheduled_at Job (ideal.processor_state Job) sched j t))
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_sched_case_analysis : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Ideal.ideal_is_idle sched t = true ∨ ∃ j, Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_sched_case_analysis
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       Or
         (@eq Bool
            (Prosa_Model_Processor_Ideal_ideal_is_idle Job
               inst_3 sched t)
            Bool_true)
         (Exists Job
            (fun j : Job =>
             Prosa_Behavior_Service_scheduled_at_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               sched j t =
             Bool_true))
```
