-- Translated from: ../rt-proofs/classic/model/schedule/uni/jitter/busy_interval.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Busy_interval

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Priority
namespace BusyInterval

section Defs

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)

variable (sched : schedule Job)
variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)

variable (higher_eq_priority : JLFP_policy Job)

variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)
