import Prosa.Implementation.Facts.JobConstructor
set_option pp.fieldNotation false

#check @Prosa.Implementation.Facts.JobConstructor.job_generation_valid_number
#check @Prosa.Implementation.Facts.JobConstructor.generate_jobs_at_unique
#check @Prosa.Implementation.Facts.JobConstructor.job_arrival_consistent
#check @Prosa.Implementation.Facts.JobConstructor.arrivals_at_unique
#check @Prosa.Implementation.Facts.JobConstructor.arrivals_between_unique
#check @Prosa.Implementation.Facts.JobConstructor.job_generation_valid_jobs

#print axioms Prosa.Implementation.Facts.JobConstructor.job_generation_valid_number
#print axioms Prosa.Implementation.Facts.JobConstructor.generate_jobs_at_unique
#print axioms Prosa.Implementation.Facts.JobConstructor.job_arrival_consistent
#print axioms Prosa.Implementation.Facts.JobConstructor.arrivals_at_unique
#print axioms Prosa.Implementation.Facts.JobConstructor.arrivals_between_unique
#print axioms Prosa.Implementation.Facts.JobConstructor.job_generation_valid_jobs
