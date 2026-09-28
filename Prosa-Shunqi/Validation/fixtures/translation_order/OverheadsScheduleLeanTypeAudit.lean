import Prosa.Analysis.Facts.Model.Overheads.Schedule
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_is_a_uniprocessor_model
#check @Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_provides_unit_supply
#check @Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_fully_consuming
#check @Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_job_dec
#check @Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_at_iff_scheduled_job
#check @Prosa.Analysis.Facts.Model.Overheads.Schedule.job_scheduled_in_busy_interval_prefix

#print axioms Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_is_a_uniprocessor_model
#print axioms Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_provides_unit_supply
#print axioms Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_fully_consuming
#print axioms Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_job_dec
#print axioms Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_at_iff_scheduled_job
#print axioms Prosa.Analysis.Facts.Model.Overheads.Schedule.job_scheduled_in_busy_interval_prefix
