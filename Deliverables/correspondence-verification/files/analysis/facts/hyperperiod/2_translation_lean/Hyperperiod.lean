-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/hyperperiod.v

import Prosa.Analysis.Definitions.Hyperperiod
import Prosa.Analysis.Facts.Periodic.TaskArrivalsSize
import Prosa.Util.Div_mod

namespace Prosa.Analysis.Facts.Hyperperiod

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Offset
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Util.Lcmseq
open Prosa.Util.Sum
open Prosa.Util.Div_mod
open Prosa.Analysis.Definitions.InfiniteJobs
open Prosa.Analysis.Definitions.Hyperperiod
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Offset
open Prosa.Analysis.Facts.Model.TaskArrivals
open Prosa.Analysis.Facts.Periodic.TaskArrivalsSize

/-! Properties of hyperperiods of periodic tasks.

Binders follow the elaborated source types: each statement takes the section inputs and hypotheses it uses, in
their elaborated order (unused section hypotheses are absent, as in the elaborated source). Representation:
`x \in s` is `decide (x ∈ s) = true`; `size` is `List.length`; `%/` is `/` on `Nat`; `a <= b < c` is
`(decide (a ≤ b) && decide (b < c)) = true`; a Boolean in `Prop` position is `= true`; the section-local
abbreviations `O_max` and `HP` are unfolded to `max_task_offset ts` and `hyperperiod ts`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-- LEAN_HELPER: equal pointwise values give equal sums over equally long ascending ranges. -/
private theorem sumSeq_range'_shift (F1 F2 : Nat → Nat) :
    ∀ (d a b : Nat), (∀ g, g < d → F1 (a + g) = F2 (b + g)) →
      sumSeq (List.range' a d) F1 = sumSeq (List.range' b d) F2
  | 0, _, _, _ => by simp [sumSeq]
  | d + 1, a, b, h => by
    have ih := sumSeq_range'_shift F1 F2 d (a + 1) (b + 1)
      (fun g hg => by
        have := h (g + 1) (by omega)
        rwa [show a + (g + 1) = a + 1 + g by omega, show b + (g + 1) = b + 1 + g by omega] at this)
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp only [sumSeq, List.range'_succ, List.map_cons, List.sum_cons] at ih ⊢
    rw [h0, ih]

/-- LEAN_HELPER: an in-range `getD` is a member of the list. -/
private theorem getD_mem_of_lt {α : Type _} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem l d h]
  exact List.getElem_mem h

section Hyperperiod

variable {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]

/-- A task set's hyperperiod is an integral multiple of each task's period in the task set. -/
theorem hyperperiod_int_mult_of_any_task (ts : TaskSet Task) (tsk : Task) :
    decide (tsk ∈ ts) = true → ∃ k : Nat, hyperperiod ts = k * task_period tsk := by
  intro hin
  have hmem : task_period tsk ∈ ts.map task_period := List.mem_map_of_mem (of_decide_eq_true hin)
  obtain ⟨c, hc⟩ := lcm_seq_is_mult_of_all_ints _ _ hmem
  exact ⟨c, by unfold hyperperiod; rw [hc, Nat.mul_comm]⟩

/-- The hyperperiod of a task set with valid periods is positive. -/
theorem valid_periods_imply_pos_hp (ts : TaskSet Task) :
    valid_periods ts → 0 < hyperperiod ts := by
  intro hvalid
  apply all_pos_implies_lcml_pos
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact of_decide_eq_true (hvalid x (decide_eq_true hx))

end Hyperperiod

section PeriodicLemmas

variable {Task : TaskType} [DecidableEq Task] [TaskOffset Task] [PeriodicModel Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

omit [TaskOffset Task] [JobArrival Job] in
/-- LEAN_HELPER: the jobs of a hyperperiod window of `tsk` are jobs of `tsk`. -/
private theorem task_of_mem_jobs_in_hyperperiod (arr_seq : arrival_sequence Job) (ts : TaskSet Task)
    (h : instant) (tsk : Task) (x : Job) (hx : x ∈ jobs_in_hyperperiod ts arr_seq h tsk) :
    job_task x = tsk := by
  unfold jobs_in_hyperperiod task_arrivals_between at hx
  exact of_decide_eq_true (List.mem_filter.mp hx).2

omit [TaskOffset Task] [JobArrival Job] in
/-- LEAN_HELPER: the jobs of a hyperperiod window arrive in the arrival sequence. -/
private theorem arrives_of_mem_jobs_in_hyperperiod (arr_seq : arrival_sequence Job) (ts : TaskSet Task)
    (h : instant) (tsk : Task) (x : Job) (hx : x ∈ jobs_in_hyperperiod ts arr_seq h tsk) :
    arrives_in arr_seq x := by
  unfold jobs_in_hyperperiod task_arrivals_between at hx
  exact in_arrivals_implies_arrived arr_seq x _ _ (decide_eq_true (List.mem_filter.mp hx).1)

/-- The job corresponding to any job `j1` in any other hyperperiod is of the same task as `j1`. -/
theorem corresponding_jobs_have_same_task (arr_seq : arrival_sequence Job) (ts : TaskSet Task) (j1 j2 : Job) :
    job_task (Task := Task) (corresponding_job_in_hyperperiod ts arr_seq j1
      (starting_instant_of_corresponding_hyperperiod ts j2) (job_task j1)) = job_task (Task := Task) j1 := by
  unfold corresponding_job_in_hyperperiod
  by_cases hi : job_index_in_hyperperiod ts arr_seq j1 (starting_instant_of_corresponding_hyperperiod ts j1)
      (job_task j1) < (jobs_in_hyperperiod ts arr_seq (starting_instant_of_corresponding_hyperperiod ts j2)
        (job_task j1)).length
  · exact task_of_mem_jobs_in_hyperperiod arr_seq ts _ _ _ (getD_mem_of_lt _ _ _ hi)
  · rw [List.getD_eq_default _ j1 (by omega)]

omit [TaskOffset Task] in
/-- A job of the hyperperiod window starting at `t` arrives in `[t, t + hyperperiod ts)`. -/
theorem all_jobs_arrive_within_hyperperiod (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (ts : TaskSet Task) (tsk : Task) (j : Job) (t : instant),
        decide (j ∈ jobs_in_hyperperiod ts arr_seq t tsk) = true →
        (decide (t ≤ job_arrival j) && decide (job_arrival j < t + hyperperiod ts)) = true := by
  intro hva ts tsk j t hj
  have hmem := of_decide_eq_true hj
  unfold jobs_in_hyperperiod task_arrivals_between at hmem
  exact in_arrivals_implies_arrived_between arr_seq hva.1 j _ _ (decide_eq_true (List.mem_filter.mp hmem).1)

/-- The number of jobs of `tsk` in the hyperperiod starting at `n1 * HP + O_max` equals the number in the one
starting at `n2 * HP + O_max`, for `n1 ≤ n2`. -/
theorem eq_size_hyp_lt (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (ts : TaskSet Task) (tsk : Task), decide (tsk ∈ ts) = true → valid_offset arr_seq tsk →
        valid_period tsk = true → respects_periodic_task_model arr_seq tsk →
        infinite_jobs (Task := Task) arr_seq →
        ∀ n1 n2 : Nat, n1 ≤ n2 →
          (jobs_in_hyperperiod ts arr_seq (n1 * hyperperiod ts + max_task_offset ts) tsk).length =
            (jobs_in_hyperperiod ts arr_seq (n2 * hyperperiod ts + max_task_offset ts) tsk).length := by
  intro hva ts tsk hin hvo hvp hper hinf n1 n2 hle
  obtain ⟨k, hk⟩ := hyperperiod_int_mult_of_any_task ts tsk hin
  have hoff : task_offset tsk ≤ max_task_offset ts := max_offset_g tsk ts hin
  unfold jobs_in_hyperperiod
  rw [size_of_task_arrivals_between, size_of_task_arrivals_between, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left]
  apply sumSeq_range'_shift
  intro g _
  have hshift := eq_size_of_task_arrivals_seperated_by_period arr_seq hva tsk hvo hvp hper hinf
    ((n2 - n1) * k) (n1 * hyperperiod ts + max_task_offset ts + g) (by omega')
  have h2 : n2 * hyperperiod ts = n1 * hyperperiod ts + (n2 - n1) * k * task_period tsk := by
    rw [Nat.mul_assoc, ← hk, ← Nat.add_mul, Nat.add_sub_cancel' hle]
  rw [hshift, h2]
  congr 2
  omega'

/-- The number of jobs of `tsk` in the hyperperiods starting at `n1 * HP + O_max` and `n2 * HP + O_max` agree. -/
theorem eq_size_of_arrivals_in_hyperperiod (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (ts : TaskSet Task) (tsk : Task), decide (tsk ∈ ts) = true → valid_offset arr_seq tsk →
        valid_period tsk = true → respects_periodic_task_model arr_seq tsk →
        infinite_jobs (Task := Task) arr_seq →
        ∀ n1 n2 : Nat,
          (jobs_in_hyperperiod ts arr_seq (n1 * hyperperiod ts + max_task_offset ts) tsk).length =
            (jobs_in_hyperperiod ts arr_seq (n2 * hyperperiod ts + max_task_offset ts) tsk).length := by
  intro hva ts tsk hin hvo hvp hper hinf n1 n2
  rcases Nat.le_total n1 n2 with h | h
  · exact eq_size_hyp_lt arr_seq hva ts tsk hin hvo hvp hper hinf n1 n2 h
  · exact (eq_size_hyp_lt arr_seq hva ts tsk hin hvo hvp hper hinf n2 n1 h).symm

/-- A job of the hyperperiod of `j2` arrives in the task arrivals up to `job_arrival j2 + HP`. -/
theorem job_in_hp_arrives_in_task_arrivals_up_to (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (ts : TaskSet Task) (tsk : Task), decide (tsk ∈ ts) = true → valid_period tsk = true →
        ∀ j1 j2 : Job, max_task_offset ts ≤ job_arrival j1 → max_task_offset ts ≤ job_arrival j2 →
        ∀ j : Job,
          decide (j ∈ jobs_in_hyperperiod ts arr_seq
            ((job_arrival j2 - max_task_offset ts) / hyperperiod ts * hyperperiod ts + max_task_offset ts)
              tsk) = true →
          decide (j ∈ task_arrivals_up_to arr_seq tsk (job_arrival j2 + hyperperiod ts)) = true := by
  intro hva ts tsk _ _ j1 j2 _ h2 j hj
  have hbounds := all_jobs_arrive_within_hyperperiod arr_seq hva ts tsk j _ hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbounds
  have hmem := of_decide_eq_true hj
  have hdiv := Nat.div_mul_le_self (job_arrival j2 - max_task_offset ts) (hyperperiod ts)
  unfold task_arrivals_up_to
  apply job_in_task_arrivals_between arr_seq hva.1 tsk j
  · exact arrives_of_mem_jobs_in_hyperperiod arr_seq ts _ tsk j hmem
  · exact task_of_mem_jobs_in_hyperperiod arr_seq ts _ tsk j hmem
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega'

/-- Job `j1` arrives in its own hyperperiod. -/
theorem job_in_own_hp (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ ts : TaskSet Task, valid_periods ts →
        ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_period tsk = true →
        ∀ j1 j2 : Job, arrives_in arr_seq j1 → job_task j1 = tsk →
          max_task_offset ts ≤ job_arrival j1 → max_task_offset ts ≤ job_arrival j2 →
          decide (j1 ∈ jobs_in_hyperperiod ts arr_seq
            ((job_arrival j1 - max_task_offset ts) / hyperperiod ts * hyperperiod ts + max_task_offset ts)
              tsk) = true := by
  intro hva ts hvps tsk _ _ j1 j2 harr htsk h1 _
  have hpos := valid_periods_imply_pos_hp ts hvps
  have hdiv := Nat.div_mul_le_self (job_arrival j1 - max_task_offset ts) (hyperperiod ts)
  have hg := div_floor_add_g (job_arrival j1 - max_task_offset ts) (hyperperiod ts) hpos
  unfold div_floor at hg
  unfold jobs_in_hyperperiod
  apply job_in_task_arrivals_between arr_seq hva.1 tsk j1 _ _ harr htsk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega'

/-- The job corresponding to `j1` in the hyperperiod of `j2` arrives in the task arrivals up to
`job_arrival j2 + HP`. -/
theorem corr_job_in_task_arrivals_up_to (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ ts : TaskSet Task, valid_periods ts →
        ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        ∀ j1 j2 : Job, arrives_in arr_seq j1 → job_task j1 = tsk →
          max_task_offset ts ≤ job_arrival j1 → max_task_offset ts ≤ job_arrival j2 →
          decide (corresponding_job_in_hyperperiod ts arr_seq j1
              (starting_instant_of_corresponding_hyperperiod ts j2) tsk ∈
            task_arrivals_up_to arr_seq tsk (job_arrival j2 + hyperperiod ts)) = true := by
  intro hva ts hvps tsk hin hvo hvp hper hinf j1 j2 harr htsk h1 h2
  apply job_in_hp_arrives_in_task_arrivals_up_to arr_seq hva ts tsk hin hvp j1 j2 h1 h2
  have hown := of_decide_eq_true
    (job_in_own_hp arr_seq hva ts hvps tsk hin hvp j1 j2 harr htsk h1 h2)
  have hsize := eq_size_of_arrivals_in_hyperperiod arr_seq hva ts tsk hin hvo hvp hper hinf
    ((job_arrival j2 - max_task_offset ts) / hyperperiod ts) ((job_arrival j1 - max_task_offset ts) / hyperperiod ts)
  apply decide_eq_true
  unfold corresponding_job_in_hyperperiod job_index_in_hyperperiod starting_instant_of_corresponding_hyperperiod
    starting_instant_of_hyperperiod hyperperiod_index
  apply getD_mem_of_lt
  rw [hsize]
  exact List.idxOf_lt_length_of_mem hown

/-- The job corresponding to `j1` in the hyperperiod of `j2` arrives in the arrival sequence. -/
theorem corresponding_job_arrives (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ ts : TaskSet Task, valid_periods ts →
        ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        ∀ j1 j2 : Job, arrives_in arr_seq j1 → job_task j1 = tsk →
          max_task_offset ts ≤ job_arrival j1 → max_task_offset ts ≤ job_arrival j2 →
          arrives_in arr_seq (corresponding_job_in_hyperperiod ts arr_seq j1
            (starting_instant_of_corresponding_hyperperiod ts j2) tsk) := by
  intro hva ts hvps tsk hin hvo hvp hper hinf j1 j2 harr htsk h1 h2
  have hmem := of_decide_eq_true
    (corr_job_in_task_arrivals_up_to arr_seq hva ts hvps tsk hin hvo hvp hper hinf j1 j2 harr htsk h1 h2)
  unfold task_arrivals_up_to task_arrivals_between at hmem
  exact in_arrivals_implies_arrived arr_seq _ _ _ (decide_eq_true (List.mem_filter.mp hmem).1)

end PeriodicLemmas

end Prosa.Analysis.Facts.Hyperperiod
