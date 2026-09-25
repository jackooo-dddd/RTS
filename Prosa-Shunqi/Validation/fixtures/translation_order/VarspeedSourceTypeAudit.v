From prosa Require Import model.processor.varspeed.

Check (@prosa.model.processor.varspeed.processor_state :
  prosa.behavior.job.JobType -> Type).
Check (@prosa.model.processor.varspeed.varspeed_scheduled_on :
  forall (Job : prosa.behavior.job.JobType), Job ->
    @prosa.model.processor.varspeed.processor_state Job -> unit -> bool).
Check (@prosa.model.processor.varspeed.varspeed_supply_on :
  forall (Job : prosa.behavior.job.JobType),
    @prosa.model.processor.varspeed.processor_state Job -> unit ->
    prosa.behavior.job.work).
Check (@prosa.model.processor.varspeed.varspeed_service_on :
  forall (Job : prosa.behavior.job.JobType), Job ->
    @prosa.model.processor.varspeed.processor_state Job -> unit ->
    prosa.behavior.job.work).
Check (@prosa.model.processor.varspeed.pstate_instance :
  forall Job : prosa.behavior.job.JobType,
    prosa.behavior.schedule.ProcessorState Job).

Print Assumptions prosa.model.processor.varspeed.pstate_instance.
