import Prosa.Model.Processor.Ideal

namespace Prosa.Validation

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

/-- Validation-only specialization of the existing translated declaration.
    Its body delegates directly to the production [ProcessorState.scheduled_in]
    with the production Ideal processor-state instance. -/
noncomputable def ideal_scheduled_in {Job : JobType} [DecidableEq Job]
    (j : Job) (s : Prosa.Model.Processor.Ideal.processor_state Job) : Bool :=
  @ProcessorState.scheduled_in
    Job (Prosa.Model.Processor.Ideal.processor_state Job)
    (Prosa.Model.Processor.Ideal.pstate_instance Job) j s

/-- Validation-only specialization of the production [scheduled_at] wrapper;
    no service-related declaration is involved. -/
noncomputable def ideal_scheduled_at {Job : JobType} [DecidableEq Job]
    (sched : schedule (Prosa.Model.Processor.Ideal.processor_state Job))
    (j : Job) (t : Prosa.Behavior.Time.instant) : Bool :=
  @Prosa.Behavior.Service.scheduled_at
    Job (Prosa.Model.Processor.Ideal.processor_state Job)
    (Prosa.Model.Processor.Ideal.pstate_instance Job) sched j t

end Prosa.Validation
