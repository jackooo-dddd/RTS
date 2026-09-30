import Prosa.Analysis.Facts.Suspension
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Suspension.suspended_implies_job_not_ready
#check @Prosa.Analysis.Facts.Suspension.suspended_implies_not_scheduled
#check @Prosa.Analysis.Facts.Suspension.suspended_implies_arrived
#check @Prosa.Analysis.Facts.Suspension.suspended_implies_pending
#check @Prosa.Analysis.Facts.Suspension.suspended_implies_not_backlogged
#check @Prosa.Analysis.Facts.Suspension.pending_and_not_suspended_implies_ready
#check @Prosa.Analysis.Facts.Suspension.suspension_bounded_trivial
#check @Prosa.Analysis.Facts.Suspension.suspension_bounded_longer_interval
#check @Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval_aux
#check @Prosa.Analysis.Facts.Suspension.exists_some_point
#check @Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval

#print axioms Prosa.Analysis.Facts.Suspension.suspended_implies_job_not_ready
#print axioms Prosa.Analysis.Facts.Suspension.suspended_implies_not_scheduled
#print axioms Prosa.Analysis.Facts.Suspension.suspended_implies_arrived
#print axioms Prosa.Analysis.Facts.Suspension.suspended_implies_pending
#print axioms Prosa.Analysis.Facts.Suspension.suspended_implies_not_backlogged
#print axioms Prosa.Analysis.Facts.Suspension.pending_and_not_suspended_implies_ready
#print axioms Prosa.Analysis.Facts.Suspension.suspension_bounded_trivial
#print axioms Prosa.Analysis.Facts.Suspension.suspension_bounded_longer_interval
#print axioms Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval_aux
#print axioms Prosa.Analysis.Facts.Suspension.exists_some_point
#print axioms Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval
