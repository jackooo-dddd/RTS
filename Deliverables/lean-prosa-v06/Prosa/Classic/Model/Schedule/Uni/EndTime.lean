-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/end_time.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 68)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime

/-!
End time of a job in a uniprocessor schedule (Rocq module `end_time`).

Representation notes:
* `diagnosis_option` and `end_time_predicate` are Lean `inductive`s with the same constructors; Rocq's
  auto-generated eliminators (`diagnosis_option_rect/_ind/_rec/_sind`, `end_time_predicate_ind/_sind`) correspond
  to Lean's auto-generated `rec`/`recOn`/`casesOn` and are not restated.
* `end_time_option` is the same structural fixpoint (on `wf`).
* The section-local `Let`s (`job_scheduled_at t := scheduled_at sched job t = true`, `job_end_time_function`,
  `job_end_time_p`, `job_completes_at`, `job_completed_by`, `job_service_during`) are unfolded.
* `c.+1` is `c + 1`, `x.-1` is `x - 1`; Boolean tests in proposition position are `= true`.
* Binder lists follow the Rocq contract (e.g. `service_eq_cost_at_end_time` takes no hypotheses and
  `job_uncompleted_before_end_time` takes only `H_valid_job`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.EndTime.end_time

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

inductive diagnosis_option : Type where
  | OK : instant → diagnosis_option
  | Failure : instant → diagnosis_option

open diagnosis_option

def end_time_option {Job : Type u} [DecidableEq Job] (sched : schedule Job) (job : Job) :
    instant → duration → Nat → diagnosis_option
  | t, 0, _ => OK t
  | t, c' + 1, 0 => Failure t
  | t, c' + 1, wf' + 1 =>
    if scheduled_at sched job t then end_time_option sched job (t + 1) c' wf'
    else end_time_option sched job (t + 1) (c' + 1) wf'

inductive end_time_predicate {Job : Type u} [DecidableEq Job] (sched : schedule Job) (job : Job) :
    instant → duration → instant → Prop where
  | C0_ : ∀ t, end_time_predicate sched job t 0 t
  | S_C_not_sched : ∀ t c e,
      ¬ (scheduled_at sched job t = true) →
      end_time_predicate sched job (t + 1) (c + 1) e →
      end_time_predicate sched job t (c + 1) e
  | S_C_sched : ∀ t c e,
      scheduled_at sched job t = true →
      end_time_predicate sched job (t + 1) c e →
      end_time_predicate sched job t (c + 1) e

def completes_at {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job)
    (job : Job) (t : instant) : Prop :=
  end_time_predicate sched job (job_arrival job) (job_cost job) t

theorem end_time_function_predicat_equivalence {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (e : instant) (wf : Nat) (t : instant) (c : duration),
      end_time_option sched job t c wf = OK e → end_time_predicate sched job t c e := by
  intro e wf
  induction wf with
  | zero =>
    intro t c H
    cases c with
    | zero => simp only [end_time_option, OK.injEq] at H; subst H; exact end_time_predicate.C0_ _
    | succ c => simp [end_time_option] at H
  | succ wf' IH =>
    intro t c H
    cases c with
    | zero => simp only [end_time_option, OK.injEq] at H; subst H; exact end_time_predicate.C0_ _
    | succ c =>
      simp only [end_time_option] at H
      cases hs : scheduled_at sched job t
      · rw [hs] at H
        exact end_time_predicate.S_C_not_sched _ _ _ (by rw [hs]; simp) (IH _ _ H)
      · rw [hs] at H
        exact end_time_predicate.S_C_sched _ _ _ hs (IH _ _ H)

theorem end_time_predicat_function_equivalence {Job : Type u} [DecidableEq Job] (job : Job)
    (sched : schedule Job) :
    ∀ (t : instant) (c : duration) (e : instant),
      end_time_predicate sched job t c e → ∃ wf : Nat, end_time_option sched job t c wf = OK e := by
  intro t c e H
  induction H with
  | C0_ t => exact ⟨1, by simp [end_time_option]⟩
  | S_C_not_sched t c e Hcase1 _ IH =>
    obtain ⟨wf, Hwf⟩ := IH
    refine ⟨wf + 1, ?_⟩
    show end_time_option sched job t (c + 1) (wf + 1) = OK e
    simp only [end_time_option]
    simp only [Bool.not_eq_true] at Hcase1
    rw [Hcase1]; exact Hwf
  | S_C_sched t c e Hcase2 _ IH =>
    obtain ⟨wf, Hwf⟩ := IH
    refine ⟨wf + 1, ?_⟩
    show end_time_option sched job t (c + 1) (wf + 1) = OK e
    simp only [end_time_option]
    rw [Hcase2]; exact Hwf

theorem end_time_predicate_not_sched {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (t : time) (c : Nat) (e : instant),
      ¬ (scheduled_at sched job t = true) →
      end_time_predicate sched job t (c + 1) e →
      end_time_predicate sched job (t + 1) (c + 1) e := by
  intro t c e Hcase1 Hpre
  cases Hpre with
  | S_C_not_sched _ _ _ _ h => exact h
  | S_C_sched _ _ _ h _ => exact absurd h Hcase1

theorem end_time_predicate_sched {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (t : time) (c : Nat) (e : instant),
      scheduled_at sched job t = true →
      end_time_predicate sched job t (c + 1) e →
      end_time_predicate sched job (t + 1) c e := by
  intro t c e Hcase2 Hpre
  cases Hpre with
  | S_C_not_sched _ _ _ h _ => exact absurd Hcase2 h
  | S_C_sched _ _ _ _ h => exact h

theorem arrival_le_end {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (t : instant) (c : duration) (e : instant), end_time_predicate sched job t c e → t ≤ e := by
  intro t c e G
  induction G with
  | C0_ t => exact Nat.le_refl _
  | S_C_not_sched t c e _ _ IH => omega'
  | S_C_sched t c e _ _ IH => omega'

theorem arrival_add_cost_le_end {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (t : instant) (c : duration) (e : instant), end_time_predicate sched job t c e → t + c ≤ e := by
  intro t c e G
  induction G with
  | C0_ t => simp
  | S_C_not_sched t c e _ _ IH => omega'
  | S_C_sched t c e _ _ IH => omega'

/-- LEAN_HELPER: peel off the first slot of `service_during`. -/
private theorem service_during_cons {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job)
    (t e : Nat) (h : t < e) :
    service_during sched j t e = service_at sched j t + service_during sched j (t + 1) e := by
  unfold service_during
  rw [Finset.sum_eq_sum_Ico_succ_bot h]

private theorem service_during_empty {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job)
    (t e : Nat) (h : e ≤ t) : service_during sched j t e = 0 := by
  unfold service_during
  rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]

/-- LEAN_HELPER: `service_eq_cost_at_end_time` for an arbitrary start and cost. -/
private theorem service_eq_cost_aux {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (t : instant) (c : duration) (e : instant), end_time_predicate sched job t c e →
      service_during sched job t e = c := by
  intro t c e job_cmplted
  induction job_cmplted with
  | C0_ t => exact service_during_empty sched job t t (Nat.le_refl _)
  | S_C_not_sched t c e Hcase1 Hpre IH =>
    have := arrival_le_end job sched _ _ _ Hpre
    rw [service_during_cons sched job t e (by omega'), IH]
    simp only [Bool.not_eq_true] at Hcase1
    simp [service_at, Hcase1]
  | S_C_sched t c e Hcase2 Hpre IH =>
    have := arrival_le_end job sched _ _ _ Hpre
    rw [service_during_cons sched job t e (by omega'), IH]
    simp [service_at, Hcase2]; omega'

theorem service_eq_cost_at_end_time {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job : Job) (sched : schedule Job) (job_end : instant) :
    completes_at job_arrival job_cost sched job job_end →
      service_during sched job (job_arrival job) job_end = job_cost job :=
  service_eq_cost_aux job sched _ _ _

theorem completed_by_end_time {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (job : Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (job_end : instant) :
    completes_at job_arrival job_cost sched job job_end → completed_by job_cost sched job job_end = true := by
  intro job_cmplted
  have LE := arrival_le_end job sched _ _ _ job_cmplted
  have SERV := service_eq_cost_at_end_time job_arrival job_cost job sched job_end job_cmplted
  unfold completed_by service service_during
  unfold service_during at SERV
  rw [ignore_service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute job 0 job_end
    (Nat.zero_le _) LE, SERV]
  simp

theorem end_time_positive {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job : Job) (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_valid_job : valid_realtime_job job_cost job_deadline job) (job_end : instant) :
    completes_at job_arrival job_cost sched job job_end → 0 < job_end := by
  intro h1
  have H_slot := H_valid_job.1
  simp only [job_cost_positive, decide_eq_true_eq] at H_slot
  have h2 := completed_by_end_time job_arrival job_cost job sched H_jobs_must_arrive_to_execute job_end h1
  simp only [completed_by, decide_eq_true_eq] at h2
  rcases Nat.eq_zero_or_pos job_end with h | h
  · subst h
    unfold service at h2
    rw [service_during_empty sched job 0 0 (Nat.le_refl _)] at h2
    omega'
  · exact h

/-- LEAN_HELPER: `job_uncompletes_at_end_time_sub_1` for an arbitrary start and cost. -/
private theorem uncompletes_aux {Job : Type u} [DecidableEq Job] (job : Job) (sched : schedule Job) :
    ∀ (t : instant) (c : duration) (e : instant), end_time_predicate sched job t c e →
      service_during sched job t (e - 1) = c - 1 := by
  intro t c e job_cmplted
  induction job_cmplted with
  | C0_ t => exact service_during_empty sched job t (t - 1) (Nat.sub_le _ _)
  | S_C_not_sched t c e Hcase1 Hpre IH =>
    have := arrival_add_cost_le_end job sched _ _ _ Hpre
    rw [service_during_cons sched job t (e - 1) (by omega'), IH]
    simp only [Bool.not_eq_true] at Hcase1
    simp [service_at, Hcase1]
  | S_C_sched t c e Hcase2 Hpre IH =>
    have := arrival_add_cost_le_end job sched _ _ _ Hpre
    cases c with
    | zero =>
      cases Hpre
      exact service_during_empty sched job t _ (by omega')
    | succ c =>
      rw [service_during_cons sched job t (e - 1) (by omega'), IH]
      simp [service_at, Hcase2]; omega'

theorem job_uncompletes_at_end_time_sub_1 {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job : Job) (sched : schedule Job) (job_end : instant) :
    completes_at job_arrival job_cost sched job job_end →
      service_during sched job (job_arrival job) (job_end - 1) = job_cost job - 1 :=
  uncompletes_aux job sched _ _ _

theorem job_uncompleted_before_end_time {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job : Job) (sched : schedule Job)
    (H_valid_job : valid_realtime_job job_cost job_deadline job) (job_end : instant) :
    completes_at job_arrival job_cost sched job job_end →
      ∀ t' : Nat, job_arrival job ≤ t' ∧ t' ≤ job_end - 1 →
        service_during sched job (job_arrival job) t' < job_cost job := by
  intro job_cmplted t' ⟨ht1, ht2⟩
  have H_slot := H_valid_job.1
  simp only [job_cost_positive, decide_eq_true_eq] at H_slot
  have SUB := job_uncompletes_at_end_time_sub_1 job_arrival job_cost job sched job_end job_cmplted
  have SPLIT : service_during sched job (job_arrival job) (job_end - 1) =
      service_during sched job (job_arrival job) t' + service_during sched job t' (job_end - 1) := by
    unfold service_during
    rw [Finset.sum_Ico_consecutive _ ht1 ht2]
  omega'

end Prosa.Classic.Model.Schedule.Uni.EndTime.end_time
