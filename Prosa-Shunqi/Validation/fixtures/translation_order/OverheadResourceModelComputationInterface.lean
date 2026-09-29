import Prosa.Model.Processor.OverheadResourceModel
import Validation.fixtures.translation_order.ScheduleChangeFactsComputationInterface

/-!
Export root for `model/processor/overhead_resource_model.v`: the ten definitions together with the accepted
overheads schedule-change facts export root and the accepted overheads processor-model root. No new equation is added.
-/

namespace Prosa.Validation.OverheadResourceModelInterface

open Prosa.Behavior.Job Prosa.Behavior.Schedule Prosa.Behavior.Time Prosa.Model.Processor.Overheads
open Prosa.Model.Processor.OverheadResourceModel

/- List-interval projections of the three `Finset.Ico` sums; each guard below requires the Lean kernel to accept
the projection as definitionally equal to the production definition (as for the accepted service projections). -/
noncomputable def timeSpentInDispatchProjection {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (oj : Option Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <| (List.range' t1 (t2 - t1) 1).map fun t =>
    (decide (scheduled_job sched t = oj) && is_dispatch sched t).toNat

noncomputable def timeSpentInContextSwitchProjection {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (oj : Option Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <| (List.range' t1 (t2 - t1) 1).map fun t =>
    (decide (scheduled_job sched t = oj) && is_context_switch sched t).toNat

noncomputable def timeSpentInCRPDProjection {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (oj : Option Job) (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <| (List.range' t1 (t2 - t1) 1).map fun t =>
    (decide (scheduled_job sched t = oj) && is_CRPD sched t).toNat

theorem timeSpentInDispatchProjection_guard :
    @time_spent_in_dispatch = @timeSpentInDispatchProjection := rfl
theorem timeSpentInContextSwitchProjection_guard :
    @time_spent_in_context_switch = @timeSpentInContextSwitchProjection := rfl
theorem timeSpentInCRPDProjection_guard :
    @time_spent_in_CRPD = @timeSpentInCRPDProjection := rfl

end Prosa.Validation.OverheadResourceModelInterface
