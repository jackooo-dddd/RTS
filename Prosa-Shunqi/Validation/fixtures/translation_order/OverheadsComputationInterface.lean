import Prosa.Model.Processor.Overheads

namespace Prosa.Validation.OverheadsInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Overheads

universe u

variable {Job : JobType} [DecidableEq Job]
variable (sched : schedule (processor_state Job))

/-!
These three projection bodies are validation-only. A projection may replace
an exported production body only when its exact whole-constant equality guard
below is checked by the Lean kernel against the freshly compiled module.
-/

noncomputable def dispatchCountProjection (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (is_dispatch sched t).toNat

noncomputable def contextSwitchCountProjection (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (is_context_switch sched t).toNat

noncomputable def crpdCountProjection (t1 t2 : instant) : Nat :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      (is_CRPD sched t).toNat

theorem dispatchCountProjection_guard :
    @total_time_in_dispatch = @dispatchCountProjection := rfl

theorem contextSwitchCountProjection_guard :
    @total_time_in_context_switch = @contextSwitchCountProjection := rfl

theorem crpdCountProjection_guard :
    @total_time_in_CRPD = @crpdCountProjection := rfl

end Prosa.Validation.OverheadsInterface
