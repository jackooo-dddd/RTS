import Prosa.Behavior.All

/-!
Kernel-elaborated probes for the zero-declaration aggregation module
`Prosa.Behavior.All`. This fixture deliberately imports only the aggregator,
then observes one public interface from every authoritative direct dependency.
-/

#check Prosa.Behavior.Time.instant
#check Prosa.Behavior.Job.JobType
#check Prosa.Behavior.Arrival_sequence.arrival_sequence
#check Prosa.Behavior.Schedule.ProcessorState
#check Prosa.Behavior.Service.scheduled_at
#check Prosa.Behavior.Ready.JobReady

def Prosa.Validation.BehaviorAllInterface.zeroInstant :
    Prosa.Behavior.Time.instant := 0

theorem Prosa.Validation.BehaviorAllInterface.zeroInstant_eq_zero :
    Prosa.Validation.BehaviorAllInterface.zeroInstant = 0 := rfl

#print axioms Prosa.Validation.BehaviorAllInterface.zeroInstant_eq_zero
