import Prosa.Behavior.Job

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Job.JobType"
#check @Prosa.Behavior.Job.JobType
#eval IO.println "FREEZE_END Prosa.Behavior.Job.JobType"
#print axioms Prosa.Behavior.Job.JobType

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Job.work"
#check @Prosa.Behavior.Job.work
#eval IO.println "FREEZE_END Prosa.Behavior.Job.work"
#print axioms Prosa.Behavior.Job.work

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Job.JobCost"
#check @Prosa.Behavior.Job.JobCost
#eval IO.println "FREEZE_END Prosa.Behavior.Job.JobCost"
#print axioms Prosa.Behavior.Job.JobCost

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Job.JobArrival"
#check @Prosa.Behavior.Job.JobArrival
#eval IO.println "FREEZE_END Prosa.Behavior.Job.JobArrival"
#print axioms Prosa.Behavior.Job.JobArrival

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Job.JobDeadline"
#check @Prosa.Behavior.Job.JobDeadline
#eval IO.println "FREEZE_END Prosa.Behavior.Job.JobDeadline"
#print axioms Prosa.Behavior.Job.JobDeadline
