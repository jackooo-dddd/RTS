import Prosa.Analysis.Facts.CompletesAt
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.CompletesAt.scheduled_at_precedes_completes_at
#check @Prosa.Analysis.Facts.CompletesAt.job_completes_at_most_once
#check @Prosa.Analysis.Facts.CompletesAt.only_one_job_completes_at_a_time
#check @Prosa.Analysis.Facts.CompletesAt.completetion_time_is_preemption_time
#check @Prosa.Analysis.Facts.CompletesAt.no_early_hep_job_completes_during_busy_prefix

#print axioms Prosa.Analysis.Facts.CompletesAt.scheduled_at_precedes_completes_at
#print axioms Prosa.Analysis.Facts.CompletesAt.job_completes_at_most_once
#print axioms Prosa.Analysis.Facts.CompletesAt.only_one_job_completes_at_a_time
#print axioms Prosa.Analysis.Facts.CompletesAt.completetion_time_is_preemption_time
#print axioms Prosa.Analysis.Facts.CompletesAt.no_early_hep_job_completes_during_busy_prefix
