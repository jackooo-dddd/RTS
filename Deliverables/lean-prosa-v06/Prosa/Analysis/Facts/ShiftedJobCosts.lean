-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/shifted_job_costs.v

import Prosa.Analysis.Facts.Hyperperiod

namespace Prosa.Analysis.Facts.ShiftedJobCosts

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Offset
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Analysis.Definitions.InfiniteJobs
open Prosa.Analysis.Definitions.Hyperperiod
open Prosa.Analysis.Facts.Hyperperiod

/-! Shifted job costs in an observation interval, and their validity.

Binders follow the elaborated source types: each declaration takes the section inputs it uses, in their elaborated
order. Representation: the source's Boolean `if` is `bif`; `a <= b < c` is `decide (a ≤ b) && decide (b < c)`; the
section-local abbreviations `O_max` and `HP` are unfolded to `max_task_offset ts` and `hyperperiod ts`; the
section-local `Instance job_costs_in_oi` is the named definition of the same name, passed explicitly where the
source's statement uses it. -/

section ValidJobCostsShifted

variable {Task : TaskType} [DecidableEq Task] [TaskOffset Task] [PeriodicModel Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]

/-- For `j` arriving after `O_max`, a job `j'` arriving in `[O_max + HP, O_max + 2HP)` gets the cost of its
corresponding job in `j`'s hyperperiod; every other job keeps its cost. -/
def job_costs_shifted (arr_seq : arrival_sequence Job) (ts : TaskSet Task) (j j' : Job) : work :=
  bif decide (max_task_offset ts ≤ job_arrival j) &&
      (decide (max_task_offset ts + hyperperiod ts ≤ job_arrival j') &&
        decide (job_arrival j' < max_task_offset ts + 2 * hyperperiod ts)) then
    job_cost (corresponding_job_in_hyperperiod ts arr_seq j'
      (starting_instant_of_corresponding_hyperperiod ts j) (job_task (Task := Task) j'))
  else job_cost j'

/-- The job costs of the observation interval (the source's section-local instance). -/
@[reducible] def job_costs_in_oi (arr_seq : arrival_sequence Job) (ts : TaskSet Task) (j : Job) : JobCost Job :=
  ⟨job_costs_shifted arr_seq ts j⟩

/-- The shifted job costs are valid. -/
theorem job_costs_shifted_valid [TaskCost Task] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : TaskSet Task, taskset_respects_periodic_task_model arr_seq ts → valid_periods ts →
        valid_offsets arr_seq ts →
        ∀ j : Job, infinite_jobs (Task := Task) arr_seq → all_jobs_from_taskset arr_seq ts →
          @arrivals_have_valid_job_costs Task _ _ Job _ _ (job_costs_in_oi arr_seq ts j) arr_seq := by
  intro hva hvalid ts hper hvps hvos j hinf hfrom j' harr
  unfold valid_job_cost
  show decide (job_costs_shifted arr_seq ts j j' ≤ task_cost (job_task (Task := Task) j')) = true
  unfold job_costs_shifted
  by_cases hc : (decide (max_task_offset ts ≤ job_arrival j) &&
      (decide (max_task_offset ts + hyperperiod ts ≤ job_arrival j') &&
        decide (job_arrival j' < max_task_offset ts + 2 * hyperperiod ts))) = true
  · rw [hc, cond_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h1, h2, _⟩ := hc
    have hin : decide (job_task (Task := Task) j' ∈ ts) = true := hfrom j' harr
    have htsk := corresponding_jobs_have_same_task arr_seq ts j' j
    have harr' := corresponding_job_arrives arr_seq hva ts hvps (job_task (Task := Task) j') hin
      (hvos _ hin) (hvps _ hin) (hper _ hin) hinf j' j harr rfl
      (by dsimp only [instant, duration] at *; omega) h1
    have hv := hvalid _ harr'
    unfold valid_job_cost at hv
    rw [htsk] at hv
    exact hv
  · rw [Bool.not_eq_true] at hc
    rw [hc, cond_false]
    exact hvalid j' harr

end ValidJobCostsShifted

end Prosa.Analysis.Facts.ShiftedJobCosts
