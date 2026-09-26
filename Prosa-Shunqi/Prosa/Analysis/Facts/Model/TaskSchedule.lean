-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/task_schedule.v

import Prosa.Analysis.Definitions.TaskSchedule
import Prosa.Analysis.Facts.Model.Scheduled
import Prosa.Model.Processor.Supply

namespace Prosa.Analysis.Facts.Model.TaskSchedule

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Definitions.TaskSchedule
open Prosa.Analysis.Facts.Model.Scheduled

/-! Facts about the task-level schedule predicates. Binders follow the
elaborated source types; the unused section classes `TaskCost`/`JobCost`
are absent there and here. `~~ b` is `(!b) = true` and Booleans in `Prop`
position are `= true`. -/

/-- A task that is served is scheduled. -/
theorem task_served_task_scheduled {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) (tsk : Task) (t : instant) :
    task_served_at arr_seq sched tsk t = true → task_scheduled_at arr_seq sched tsk t = true := by
  unfold task_served_at task_scheduled_at served_jobs_of_task_at
  cases scheduled_jobs_of_task_at arr_seq sched tsk t with
  | nil => simp
  | cons _ _ => simp

private theorem mem_scheduled_jobs_of_task {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) (tsk : Task) (t : instant) (j : Job) :
    j ∈ scheduled_jobs_of_task_at arr_seq sched tsk t ↔
      j ∈ scheduled_jobs_at arr_seq sched t ∧ job_of_task tsk j = true := by
  unfold scheduled_jobs_of_task_at
  simp [List.mem_filter]

/-- Under ideal progress, served and scheduled coincide. -/
theorem task_served_eq_task_scheduled {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (PState : ProcessorState Job) (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ tsk : Task, ideal_progress_proc_model PState →
      ∀ t : instant, task_served_at arr_seq sched tsk t = task_scheduled_at arr_seq sched tsk t := by
  intro hva PState sched hfrom hmust tsk hprog t
  cases hs : task_scheduled_at arr_seq sched tsk t
  · cases hv : task_served_at arr_seq sched tsk t
    · rfl
    · have := task_served_task_scheduled arr_seq sched tsk t hv
      rw [hs] at this; exact absurd this (by decide)
  · unfold task_scheduled_at at hs
    cases hl : scheduled_jobs_of_task_at arr_seq sched tsk t with
    | nil => rw [hl] at hs; simp at hs
    | cons j js =>
      have hj : j ∈ scheduled_jobs_of_task_at arr_seq sched tsk t := by rw [hl]; exact List.mem_cons_self
      have hsj := ((mem_scheduled_jobs_of_task arr_seq sched tsk t j).1 hj).1
      have hsched : scheduled_at sched j t = true := by
        have := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j t
        rw [decide_eq_true hsj] at this; exact this.symm
      have hrec : receives_service_at sched j t = true := decide_eq_true (hprog j (sched t) hsched)
      have hmem : j ∈ served_jobs_of_task_at arr_seq sched tsk t := by
        unfold served_jobs_of_task_at; rw [List.mem_filter]; exact ⟨hj, hrec⟩
      unfold task_served_at
      cases hsv : served_jobs_of_task_at arr_seq sched tsk t with
      | nil => rw [hsv] at hmem; exact absurd hmem List.not_mem_nil
      | cons _ _ => rfl

/-- An idle processor schedules no task. -/
theorem no_task_scheduled_when_idle {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (PState : ProcessorState Job) (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (t : instant),
        is_idle arr_seq sched t = true → (!task_scheduled_at arr_seq sched tsk t) = true := by
  intro _ PState sched _ _ tsk t hidle
  unfold is_idle at hidle
  unfold task_scheduled_at scheduled_jobs_of_task_at
  rw [List.isEmpty_iff] at hidle
  rw [hidle]; rfl

/-- An idle processor serves no task. -/
theorem no_task_served_when_idle {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (PState : ProcessorState Job) (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (t : instant),
        is_idle arr_seq sched t = true → (!task_served_at arr_seq sched tsk t) = true := by
  intro hva PState sched hfrom hmust tsk t hidle
  have h := no_task_scheduled_when_idle arr_seq hva PState sched hfrom hmust tsk t hidle
  cases hv : task_served_at arr_seq sched tsk t
  · rfl
  · have := task_served_task_scheduled arr_seq sched tsk t hv
    rw [this] at h; exact absurd h (by decide)

private theorem scheduled_jobs_at_singleton {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (hva : valid_arrival_sequence arr_seq)
    {PState : ProcessorState Job} (huni : uniprocessor_model PState) (sched : schedule PState)
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq)
    (hmust : jobs_must_arrive_to_execute sched) (j : Job) (t : instant)
    (hs : scheduled_at sched j t = true) :
    scheduled_jobs_at arr_seq sched t = [j] := by
  have := scheduled_jobs_at_scheduled_at arr_seq hva sched hfrom hmust huni j t
  rw [hs] at this; exact of_decide_eq_true this

/-- A scheduled job determines whether its task is scheduled. -/
theorem job_of_scheduled_task {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (j : Job) (t : instant),
        scheduled_at sched j t = true →
          task_scheduled_at arr_seq sched tsk t = job_of_task tsk j := by
  intro hva PState huni sched hfrom hmust tsk j t hs
  unfold task_scheduled_at scheduled_jobs_of_task_at
  rw [scheduled_jobs_at_singleton arr_seq hva huni sched hfrom hmust j t hs]
  cases h : job_of_task tsk j <;> simp [h]

/-- A scheduled job of the task makes the task scheduled. -/
theorem job_of_task_scheduled {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (j : Job) (t : instant),
        job_of_task tsk j = true → scheduled_at sched j t = true →
          task_scheduled_at arr_seq sched tsk t = true := by
  intro hva PState huni sched hfrom hmust tsk j t htsk hs
  rw [job_of_scheduled_task arr_seq hva PState huni sched hfrom hmust tsk j t hs]; exact htsk

/-- A scheduled job of another task makes the task not scheduled. -/
theorem job_of_other_task_scheduled {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (j : Job) (t : instant),
        (!job_of_task tsk j) = true → scheduled_at sched j t = true →
          (!task_scheduled_at arr_seq sched tsk t) = true := by
  intro hva PState huni sched hfrom hmust tsk j t htsk hs
  rw [job_of_scheduled_task arr_seq hva PState huni sched hfrom hmust tsk j t hs]; exact htsk

/-- A scheduled job of another task makes the task not served. -/
theorem job_of_other_task_scheduled' {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (j : Job) (t : instant),
        (!job_of_task tsk j) = true → scheduled_at sched j t = true →
          (!task_served_at arr_seq sched tsk t) = true := by
  intro hva PState huni sched hfrom hmust tsk j t htsk hs
  have h := job_of_other_task_scheduled arr_seq hva PState huni sched hfrom hmust tsk j t htsk hs
  cases hv : task_served_at arr_seq sched tsk t
  · rfl
  · have := task_served_task_scheduled arr_seq sched tsk t hv
    rw [this] at h; exact absurd h (by decide)

/-- A scheduled job of the task that receives no service leaves the task unserved. -/
theorem job_of_task_not_served {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (j : Job) (t : instant),
        scheduled_at sched j t = true → job_of_task tsk j = true → service_at sched j t = 0 →
          (!task_served_at arr_seq sched tsk t) = true := by
  intro hva PState huni sched hfrom hmust tsk j t hs htsk hz
  unfold task_served_at served_jobs_of_task_at scheduled_jobs_of_task_at
  rw [scheduled_jobs_at_singleton arr_seq hva huni sched hfrom hmust j t hs]
  have hr : receives_service_at sched j t = false := by
    unfold receives_service_at; rw [hz]; rfl
  simp [htsk, hr]

/-- On a fully-consuming uniprocessor with supply, a scheduled job decides
whether its task is served. -/
theorem task_served_at_eq_job_of_task {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ tsk : Task, fully_consuming_proc_model PState →
      ∀ t : instant, has_supply sched t = true →
      ∀ j : Job, scheduled_at sched j t = true →
        task_served_at arr_seq sched tsk t = job_of_task tsk j := by
  intro hva PState huni sched hfrom hmust tsk hfull t hsup j hs
  have hr : receives_service_at sched j t = true := by
    unfold receives_service_at
    rw [hfull j sched t hs]
    exact hsup
  unfold task_served_at served_jobs_of_task_at scheduled_jobs_of_task_at
  rw [scheduled_jobs_at_singleton arr_seq hva huni sched hfrom hmust j t hs]
  cases htsk : job_of_task tsk j <;> simp [htsk, hr]

end Prosa.Analysis.Facts.Model.TaskSchedule
