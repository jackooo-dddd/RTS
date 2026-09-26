-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/ideal/service_of_jobs.v

import Prosa.Model.Aggregate.ServiceOfJobs
import Prosa.Model.Processor.Supply
import Prosa.Model.Processor.PlatformProperties
import Prosa.Model.Schedule.Scheduled
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Analysis.Facts.Behavior.Arrivals
open scoped BigOperators

/-! Service received by sets of jobs on uniprocessors with idle times.
`predT` is `fun _ => true`; `t1 <= t < t2` is the Boolean conjunction of
decides; the unused section classes `JobTask`/`JobCost`, the unused
hypothesis `completed_jobs_dont_execute` and the unused predicate `P` are
absent from the elaborated types and here. -/

/-- Exchange of the finite job-list sum with the interval sum. -/
private theorem list_sum_interval_exchange {Job : JobType} (L : List Job)
    (f : Job → Nat → Nat) (t1 t2 : Nat) :
    (L.map fun j => ∑ t ∈ Finset.Ico t1 t2, f j t).sum =
      ∑ t ∈ Finset.Ico t1 t2, (L.map fun j => f j t).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- `service_of_jobs` over all jobs as an interval sum of per-instant sums. -/
private theorem service_of_jobs_predT_eq {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (L : List Job)
    (t1 t2 : instant) :
    service_of_jobs sched (fun _ => true) L t1 t2 =
      ∑ t ∈ Finset.Ico t1 t2, (L.map fun j => service_at sched j t).sum := by
  unfold service_of_jobs Prosa.Util.Sum.sumFiltered
  rw [List.filter_true]
  exact list_sum_interval_exchange L (fun j t => service_at sched j t) t1 t2

/-- A non-idle instant has a scheduled job among the arrivals up to it. -/
private theorem nonidle_scheduled_job {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (t : instant) :
    is_idle arr_seq sched t = false →
      ∃ j, j ∈ arrivals_up_to arr_seq t ∧ scheduled_at sched j t = true := by
  intro h
  unfold is_idle at h
  cases hs : scheduled_jobs_at arr_seq sched t with
  | nil => rw [hs] at h; simp at h
  | cons j js =>
    have hm : j ∈ scheduled_jobs_at arr_seq sched t := by rw [hs]; exact List.mem_cons_self
    unfold scheduled_jobs_at at hm
    rw [List.mem_filter] at hm
    exact ⟨j, hm.1, hm.2⟩

/-- A job arrived by `t < t2` is among the arrivals in `[0, t2)`. -/
private theorem arrivals_up_to_mem_between {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) (j : Job) (t t2 : instant) (ht : t < t2) :
    j ∈ arrivals_up_to arr_seq t → j ∈ arrivals_between arr_seq 0 t2 := by
  intro h
  exact of_decide_eq_true (arrivals_between_sub arr_seq j 0 0 (t + 1) t2 (Nat.le_refl 0) ht
    (decide_eq_true h))

/-- A member's value is bounded by the list sum. -/
private theorem le_map_sum_of_mem {Job : JobType} (L : List Job) (f : Job → Nat) (j : Job)
    (h : j ∈ L) : f j ≤ (L.map f).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

/-- If the total blackout plus the total service in `[t1, t2)` is below
`t2 - t1` on a fully-consuming uniprocessor, some instant in `[t1, t2)` is idle. -/
theorem low_service_implies_existence_of_idle_time_rs (Job : JobType) [DecidableEq Job]
    [JobArrival Job] (PState : ProcessorState Job) :
    uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ t1 t2 : instant,
        blackout_during sched t1 t2 +
            service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 t2) t1 t2 <
          t2 - t1 →
        ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧
          is_idle arr_seq sched t = true := by
  intro _ hfull arr_seq _ sched _ _ t1 t2 hlow
  by_contra hno
  have hbusy : ∀ t ∈ Finset.Ico t1 t2, 1 ≤ (is_blackout sched t).toNat +
      ((arrivals_between arr_seq 0 t2).map fun j => service_at sched j t).sum := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hidle : is_idle arr_seq sched t = false := by
      cases hi : is_idle arr_seq sched t
      · rfl
      · exact absurd ⟨t, by simp [ht.1, ht.2], hi⟩ hno
    obtain ⟨j, hj, hs⟩ := nonidle_scheduled_job arr_seq sched t hidle
    have hmem := arrivals_up_to_mem_between arr_seq j t t2 ht.2 hj
    cases hb : is_blackout sched t
    · have hsup : has_supply sched t = true := by
        unfold is_blackout at hb; cases h : has_supply sched t <;> simp_all
      have hpos : 0 < supply_at sched t := of_decide_eq_true hsup
      have hserv : service_at sched j t = supply_at sched t := hfull j sched t hs
      have := le_map_sum_of_mem (arrivals_between arr_seq 0 t2)
        (fun j => service_at sched j t) j hmem
      simp only [Bool.toNat_false, Nat.zero_add]
      exact Nat.le_trans (by rw [hserv]; exact hpos) this
    · simp [Bool.toNat_true]
  have hsum : t2 - t1 ≤ blackout_during sched t1 t2 +
      service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 t2) t1 t2 := by
    rw [service_of_jobs_predT_eq]
    unfold blackout_during
    rw [← Finset.sum_add_distrib]
    calc t2 - t1 = ∑ _t ∈ Finset.Ico t1 t2, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hbusy
  exact absurd hlow (Nat.not_lt.mpr hsum)

/-- If the total service in `[t1, t2)` is below `t2 - t1` on an
ideal-progress uniprocessor, some instant in `[t1, t2)` is idle. -/
theorem low_service_implies_existence_of_idle_time (Job : JobType) [DecidableEq Job]
    [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job,
      uniprocessor_model PState → ideal_progress_proc_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ t1 t2 : instant,
        service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 t2) t1 t2 < t2 - t1 →
        ∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧
          is_idle arr_seq sched t = true := by
  intro _ PState _ hprog sched _ _ t1 t2 hlow
  by_contra hno
  have hbusy : ∀ t ∈ Finset.Ico t1 t2,
      1 ≤ ((arrivals_between arr_seq 0 t2).map fun j => service_at sched j t).sum := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hidle : is_idle arr_seq sched t = false := by
      cases hi : is_idle arr_seq sched t
      · rfl
      · exact absurd ⟨t, by simp [ht.1, ht.2], hi⟩ hno
    obtain ⟨j, hj, hs⟩ := nonidle_scheduled_job arr_seq sched t hidle
    have hmem := arrivals_up_to_mem_between arr_seq j t t2 ht.2 hj
    have hpos : 0 < service_at sched j t := hprog j (sched t) hs
    exact Nat.le_trans hpos (le_map_sum_of_mem (arrivals_between arr_seq 0 t2)
      (fun j => service_at sched j t) j hmem)
  have hsum : t2 - t1 ≤
      service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 t2) t1 t2 := by
    rw [service_of_jobs_predT_eq]
    calc t2 - t1 = ∑ _t ∈ Finset.Ico t1 t2, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hbusy
  exact absurd hlow (Nat.not_lt.mpr hsum)

end Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs
