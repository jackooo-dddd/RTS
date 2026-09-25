import Prosa.Model.Task.AbsoluteDeadline

#check @Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline
#print Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline
#print axioms Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline

section InstanceSelection
  open Prosa.Behavior.Job Prosa.Model.Task.Concept
  variable {Job : JobType} [DecidableEq Job]
  variable {Task : TaskType} [DecidableEq Task]
  variable [TaskDeadline Task] [JobArrival Job] [JobTask Job Task]
  #synth JobDeadline Job
  example (j : Job) :
      job_deadline j =
        job_arrival j + task_deadline (job_task (Task := Task) j) := by
    rfl
end InstanceSelection
