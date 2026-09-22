From prosa Require Import behavior.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJob.

(** Source types are elaborated from the byte-identical official v0.6 file. *)
Check @prosa.behavior.job.JobType.
Check @prosa.behavior.job.work.
Check @prosa.behavior.job.JobCost.
Check @prosa.behavior.job.job_cost.
Check @prosa.behavior.job.JobArrival.
Check @prosa.behavior.job.job_arrival.
Check @prosa.behavior.job.JobDeadline.
Check @prosa.behavior.job.job_deadline.

(** Target types come from the actual compiled and imported Lean artifact. *)
Check ImportedJob.Prosa_Behavior_Job_JobType.
Check ImportedJob.Prosa_Behavior_Job_work.
Check ImportedJob.Prosa_Behavior_Job_JobCost.
Check ImportedJob.Prosa_Behavior_Job_JobCost_mk.
Check ImportedJob.Prosa_Behavior_Job_JobCost_job_cost.
Check ImportedJob.Prosa_Behavior_Job_JobArrival.
Check ImportedJob.Prosa_Behavior_Job_JobArrival_mk.
Check ImportedJob.Prosa_Behavior_Job_JobArrival_job_arrival.
Check ImportedJob.Prosa_Behavior_Job_JobDeadline.
Check ImportedJob.Prosa_Behavior_Job_JobDeadline_mk.
Check ImportedJob.Prosa_Behavior_Job_JobDeadline_job_deadline.
