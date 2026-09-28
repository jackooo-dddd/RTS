import Prosa.Analysis.Facts.BusyInterval.All

/-!
Aggregator-only interface probe for `analysis/facts/busy_interval/all.v`: it
uses one declaration from each re-exported module through the aggregator import
only.
-/

namespace Prosa.Validation.FactsBusyIntervalAllInterface

theorem facts_busy_interval_all_exposes_modules : True := by
  have _h1 := @Prosa.Analysis.Facts.BusyInterval.Arrival.busy_interval_job_arrival.{0, 0, 0}
  have _h2 := @Prosa.Analysis.Facts.BusyInterval.CarryIn.no_carry_in_at_zero.{0, 0, 0}
  have _h3 := @Prosa.Analysis.Facts.BusyInterval.QuietTime.zero_is_quiet_time.{0, 0, 0}
  have _h4 := @Prosa.Analysis.Facts.BusyInterval.Existence.exists_busy_interval.{0, 0, 0, 0}
  have _h5 := @Prosa.Analysis.Facts.BusyInterval.HepAtPt.instant_t_is_not_idle.{0, 0, 0}
  have _h6 := @Prosa.Analysis.Facts.BusyInterval.PiBound.priority_inversion_is_bounded.{0, 0, 0, 0}
  trivial

#print axioms facts_busy_interval_all_exposes_modules

end Prosa.Validation.FactsBusyIntervalAllInterface
