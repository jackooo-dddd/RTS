import Prosa.Analysis.Facts.Behavior.Deadlines
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_later_deadline
#check @Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_scheduled_later
#check @Prosa.Analysis.Facts.Behavior.Deadlines.scheduled_at_implies_later_deadline
#check @Prosa.Analysis.Facts.Behavior.Deadlines.service_invariant_implies_deadline_met

#print axioms Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_later_deadline
#print axioms Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_scheduled_later
#print axioms Prosa.Analysis.Facts.Behavior.Deadlines.scheduled_at_implies_later_deadline
#print axioms Prosa.Analysis.Facts.Behavior.Deadlines.service_invariant_implies_deadline_met
