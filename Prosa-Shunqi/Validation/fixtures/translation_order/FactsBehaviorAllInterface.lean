import Prosa.Analysis.Facts.Behavior.All

/-!
Aggregator-only interface probe for `analysis/facts/behavior/all.v`: it uses
one declaration from each re-exported module through the aggregator import
only.
-/

namespace Prosa.Validation.FactsBehaviorAllInterface

theorem facts_behavior_all_exposes_modules : True := by
  have _h1 := @Prosa.Analysis.Facts.Behavior.Service.service0.{0, 0, 0}
  have _h2 := @Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic.{0, 0, 0}
  have _h3 := @Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_before.{0}
  have _h4 := @Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_later_deadline.{0, 0, 0}
  trivial

#print axioms facts_behavior_all_exposes_modules

end Prosa.Validation.FactsBehaviorAllInterface
