import Prosa.Classic.Model.Arrival.Basic.Job
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.job_cost_positive
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.job_deadline_positive
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.job_cost_le_deadline
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.valid_realtime_job
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.job_cost_le_task_cost
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.job_deadline_eq_task_deadline
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.valid_sporadic_job
#check @Prosa.Classic.Model.Arrival.Basic.Job.Job.cost_of_jobs_from_arrival_sequence_le_task_cost

#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.job_cost_positive
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.job_deadline_positive
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.job_cost_le_deadline
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.valid_realtime_job
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.job_cost_le_task_cost
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.job_deadline_eq_task_deadline
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.valid_sporadic_job
#print axioms Prosa.Classic.Model.Arrival.Basic.Job.Job.cost_of_jobs_from_arrival_sequence_le_task_cost
