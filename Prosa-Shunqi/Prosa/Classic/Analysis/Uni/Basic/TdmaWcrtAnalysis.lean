-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/basic/tdma_wcrt_analysis.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 92)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma
import Prosa.Classic.Model.Schedule.Uni.EndTime

/-!
Exact response-time analysis of a job under TDMA on a uniprocessor (Rocq module `WCRT_OneJobTDMA`).

Representation notes:
* `{set sporadic_task}` is the v0.6 sequence-set `Prosa.Util.Seqset.set`; `tsk \in ts` is `tsk ∈ ts`.
* The section-local `Let`s `time_slot`, `slot_offset`, `tdma_cycle`, `is_scheduled_at`, `in_time_slot_at`,
  `pending_at`, `job_end_time_predicate`, `job_completes_at` and `WCET` are unfolded; the arithmetic `Let`s
  `from_start_of_slot`, `to_next_slot`, `duration_to_finish_from_start_of_slot_with` and `to_end_of_slot` are kept as
  `LEAN_HELPER` definitions of the same names (taking the section variables they use).
* `x %% m` is `x % m`; `c == 0` in `if` is `c = 0`; `c <= x` in `if` is `c ≤ x`; `x.-1` is `x - 1`; `x.+1` is `x + 1`;
  `div_ceil` is the classic `Prosa.Classic.Util.DivMod.div_ceil`.
* `reflect P b` (the `TDMA_policy_case_RT_le_Period` statement, an informative type) is the informative
  `BoolReflect P b`, so that lemma is a `def`.
* Boolean tests in proposition position are `= true`.
* Binder lists follow the Rocq contract (each lemma takes exactly the section variables and hypotheses Rocq
  abstracts, e.g. `pendingSt_Sched` takes the TDMA parameters and `H_valid_time_slot` but not `TDMA_policy`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.PolicyTdma.PolicyTDMA
open Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma.Platform_TDMA
open Prosa.Classic.Model.Schedule.Uni.EndTime.end_time
open Prosa.Classic.Util.DivMod (div_ceil ceil_eq1 ceil_suba ceil_neq0 leq_divceil2r)
open Prosa.Classic.Util.List (BoolReflect)
open Prosa.Util.Seqset

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### `LEAN_HELPER` definitions for the section-local arithmetic `Let`s -/

/-- LEAN_HELPER (Rocq `Let from_start_of_slot`). -/
def from_start_of_slot {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (t : time) : Nat :=
  (t + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot) % TDMA_cycle ts task_time_slot

/-- LEAN_HELPER (Rocq `Let to_next_slot`). -/
def to_next_slot {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (t : time) : Nat :=
  TDMA_cycle ts task_time_slot - from_start_of_slot task_time_slot slot_order ts tsk t

/-- LEAN_HELPER (Rocq `Let duration_to_finish_from_start_of_slot_with`). -/
def duration_to_finish_from_start_of_slot_with {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task)
    (ts : set sporadic_task) (tsk : sporadic_task) (c : time) : duration :=
  (div_ceil c (task_time_slot tsk) - 1) * (TDMA_cycle ts task_time_slot - task_time_slot tsk) + c

/-- LEAN_HELPER (Rocq `Let to_end_of_slot`). -/
def to_end_of_slot {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (t : time) : Nat :=
  task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk t

def formula_rt {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (arr : instant) (c : duration) : Nat :=
  if c = 0 then 0 else
  if Task_in_time_slot ts slot_order tsk task_time_slot arr then
    if c ≤ to_end_of_slot task_time_slot slot_order ts tsk arr then c
    else to_next_slot task_time_slot slot_order ts tsk arr + duration_to_finish_from_start_of_slot_with task_time_slot ts tsk (c - to_end_of_slot task_time_slot slot_order ts tsk arr)
  else to_next_slot task_time_slot slot_order ts tsk arr + duration_to_finish_from_start_of_slot_with task_time_slot ts tsk c

def job_response_time_tdma_in_at_most_one_job_is_pending {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task)
    (j : Job) : Nat :=
  formula_rt task_time_slot slot_order ts tsk (job_arrival j) (job_cost j)

/-! ### Proof-local arithmetic facts -/

private theorem in_slot_iff {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (t : time) :
    Task_in_time_slot ts slot_order tsk task_time_slot t = true ↔ from_start_of_slot task_time_slot slot_order ts tsk t < task_time_slot tsk :=
  ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

private theorem in_slot_false_iff {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (t : time) :
    Task_in_time_slot ts slot_order tsk task_time_slot t = false ↔ task_time_slot tsk ≤ from_start_of_slot task_time_slot slot_order ts tsk t := by
  constructor
  · intro h; by_contra hc; rw [(in_slot_iff task_time_slot slot_order ts tsk t).mpr (by omega')] at h; exact Bool.noConfusion h
  · intro h; cases hh : Task_in_time_slot ts slot_order tsk task_time_slot t
    · rfl
    · have := (in_slot_iff task_time_slot slot_order ts tsk t).mp hh; omega'

private theorem fs_lt {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (hc : 0 < TDMA_cycle ts task_time_slot) (t : time) : from_start_of_slot task_time_slot slot_order ts tsk t < TDMA_cycle ts task_time_slot :=
  Nat.mod_lt _ hc

private theorem fs_add {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (hc : 0 < TDMA_cycle ts task_time_slot) (t d : Nat) : from_start_of_slot task_time_slot slot_order ts tsk (t + d) = (from_start_of_slot task_time_slot slot_order ts tsk t + d) % TDMA_cycle ts task_time_slot := by
  unfold from_start_of_slot
  have ho : Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot < TDMA_cycle ts task_time_slot := Nat.mod_lt _ hc
  rw [Nat.mod_add_mod, show t + d + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot =
    t + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot + d by omega']

private theorem fs_succ_lt {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (hc : 0 < TDMA_cycle ts task_time_slot) (t : Nat) (h : from_start_of_slot task_time_slot slot_order ts tsk t + 1 < TDMA_cycle ts task_time_slot) :
    from_start_of_slot task_time_slot slot_order ts tsk (t + 1) = from_start_of_slot task_time_slot slot_order ts tsk t + 1 := by
  rw [fs_add task_time_slot slot_order ts tsk hc, Nat.mod_eq_of_lt h]

private theorem fs_succ_eq {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (hc : 0 < TDMA_cycle ts task_time_slot) (t : Nat) (h : from_start_of_slot task_time_slot slot_order ts tsk t + 1 = TDMA_cycle ts task_time_slot) :
    from_start_of_slot task_time_slot slot_order ts tsk (t + 1) = 0 := by
  rw [fs_add task_time_slot slot_order ts tsk hc, h, Nat.mod_self]

private theorem fs_next {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (hc : 0 < TDMA_cycle ts task_time_slot) (t : Nat) : from_start_of_slot task_time_slot slot_order ts tsk (t + to_next_slot task_time_slot slot_order ts tsk t) = 0 := by
  have hlt := fs_lt task_time_slot slot_order ts tsk hc t
  unfold to_next_slot
  rw [fs_add task_time_slot slot_order ts tsk hc, show from_start_of_slot task_time_slot slot_order ts tsk t + (TDMA_cycle ts task_time_slot - from_start_of_slot task_time_slot slot_order ts tsk t) = TDMA_cycle ts task_time_slot by omega', Nat.mod_self]

/-- LEAN_HELPER: `m * x = (m - 1) * x + x` for positive `m`. -/
private theorem mul_pred_add (m x : Nat) (hm : 0 < m) : m * x = (m - 1) * x + x := by
  conv => lhs; rw [show m = (m - 1) + 1 by omega']
  rw [Nat.add_mul, Nat.one_mul]

private theorem service_step {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat) :
    service sched j (t + 1) = service sched j t + service_at sched j t := by
  unfold service service_during
  rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]

/-! ### Basic lemmas -/

theorem at_most_one_job_is_pending {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (j : Job)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (j_other : Job) (t : time), arrives_in arr_seq j_other → job_arrival j_other < job_arrival j →
      pending job_arrival job_cost sched j t = true → pending job_arrival job_cost sched j_other t = true →
      job_task j = job_task j_other → j = j_other := by
  intro j_other t ARRJO ARRBF PJ PJO EQTSK
  exfalso
  simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at PJ PJO
  have ARRJ := of_decide_eq_true PJ.1
  have C := all_previous_jobs_of_same_task_completed j_other ARRJO EQTSK ARRBF
  have C2 := completion_monotonic job_cost sched j_other _ t ARRJ C
  rw [C2] at PJO; exact Bool.noConfusion PJO.2

def TDMA_policy_case_RT_le_Period {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (j : Job)
    (H_job_task : job_task j = tsk) (job_in_arr_seq : arrives_in arr_seq j)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ t, pending job_arrival job_cost sched j t = true → BoolReflect (Task_in_time_slot ts slot_order tsk task_time_slot t = true) (scheduled_at sched j t) := by
  intro t PEN
  cases hs : scheduled_at sched j t
  · apply BoolReflect.isFalse
    intro INSLOT
    have BACK : backlogged job_arrival job_cost sched j t = true := by simp [backlogged, PEN, hs]
    rcases (TDMA_policy j t job_in_arr_seq).2 BACK with NIN | ⟨j_other, ARRJO, ARRBF, SAME, SCHEDJO⟩
    · rw [H_job_task] at NIN; exact NIN INSLOT
    · have PJO := scheduled_implies_pending job_arrival job_cost sched H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute j_other t SCHEDJO
      have EQ := at_most_one_job_is_pending job_arrival job_cost job_task arr_seq sched j
        all_previous_jobs_of_same_task_completed j_other t ARRJO ARRBF PEN PJO SAME
      subst EQ; rw [hs] at SCHEDJO; exact Bool.noConfusion SCHEDJO
  · apply BoolReflect.isTrue
    have := (TDMA_policy j t job_in_arr_seq).1 hs
    rwa [H_job_task] at this

/-- LEAN_HELPER: the reflection view as an equation. -/
private theorem sched_eq_in_slot {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) (t : time) (PEN : pending job_arrival job_cost sched j t = true) :
    scheduled_at sched j t = Task_in_time_slot ts slot_order tsk task_time_slot t := by
  have R := TDMA_policy_case_RT_le_Period job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute task_time_slot slot_order ts tsk j H_job_task job_in_arr_seq TDMA_policy all_previous_jobs_of_same_task_completed
    t PEN
  revert R
  cases scheduled_at sched j t <;> cases Task_in_time_slot ts slot_order tsk task_time_slot t <;> intro R <;> cases R <;>
    first | rfl | (exfalso; contradiction)

theorem pendingArrival {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (j : Job)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) :
    pending job_arrival job_cost sched j (job_arrival j) = true := by
  have POS := H_valid_job.1.1
  simp only [job_cost_positive, decide_eq_true_eq] at POS
  have Z := cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0
    (job_arrival j) (Nat.le_refl _)
  have NC : ¬ (job_cost j ≤ service sched j (job_arrival j)) := by
    unfold service service_during; rw [Z]; omega'
  simp only [pending, has_arrived, completed_by, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨decide_eq_true (Nat.le_refl _), decide_eq_false NC⟩

theorem pendingSt {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job) (j : Job) :
    ∀ t : time, pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false → pending job_arrival job_cost sched j (t + 1) = true := by
  intro t PEN NSCHED
  simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at PEN ⊢
  have ARR := of_decide_eq_true PEN.1
  have NC : ¬ (job_cost j ≤ service sched j t) := fun h => by
    have hc : completed_by job_cost sched j t = true := decide_eq_true h
    rw [hc] at PEN; exact Bool.noConfusion PEN.2
  refine ⟨decide_eq_true (by omega'), decide_eq_false ?_⟩
  rw [service_step]
  simp only [service_at, NSCHED, Bool.toNat_false, Nat.add_zero]
  exact NC

theorem pendingSt_Sched {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job) (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task)
    (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true) :
    ∀ (t : time) (c : Nat), pending job_arrival job_cost sched j t = true → service sched j t + (c + 2) = job_cost j → scheduled_at sched j t = true →
      pending job_arrival job_cost sched j (t + 1) = true := by
  intro t c PEN COST SCHED
  simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at PEN ⊢
  have ARR := of_decide_eq_true PEN.1
  refine ⟨decide_eq_true (by omega'), decide_eq_false ?_⟩
  rw [service_step]
  simp only [service_at, SCHED, Bool.toNat_true]
  omega'

/-! ### The response-time formula and the end-time predicate -/

theorem to_next_slot_pos {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true) :
    ∀ t : Nat, 0 < to_next_slot task_time_slot slot_order ts tsk t := by
  intro t
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have := fs_lt task_time_slot slot_order ts tsk hc t
  unfold to_next_slot; omega'

theorem lt_to_next_slot_1LR {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true) :
    ∀ a t : Nat, a + 1 < to_next_slot task_time_slot slot_order ts tsk t → a < to_next_slot task_time_slot slot_order ts tsk (t + 1) := by
  intro a t h
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have hlt := fs_lt task_time_slot slot_order ts tsk hc t
  unfold to_next_slot at h ⊢
  rcases Nat.lt_or_ge (from_start_of_slot task_time_slot slot_order ts tsk t + 1) (TDMA_cycle ts task_time_slot) with h1 | h1
  · rw [fs_succ_lt task_time_slot slot_order ts tsk hc t h1]; omega'
  · rw [fs_succ_eq task_time_slot slot_order ts tsk hc t (by omega')]; omega'

theorem lt_to_next_slot_LR {sporadic_task : Type u} [DecidableEq sporadic_task] (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true) :
    ∀ b a t : Nat, a + b < to_next_slot task_time_slot slot_order ts tsk t → a < to_next_slot task_time_slot slot_order ts tsk (t + b) := by
  intro b
  induction b with
  | zero => intro a t h; simpa using h
  | succ b IH =>
    intro a t h
    rw [← Nat.add_assoc]
    exact lt_to_next_slot_1LR task_time_slot slot_order ts tsk H_task_in_task_set H_valid_time_slot a (t + b) (IH (a + 1) t (by omega'))

theorem S_t_not_sched {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ t : time, pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false → 1 < to_next_slot task_time_slot slot_order ts tsk t → scheduled_at sched j (t + 1) = false := by
  intro t PEN NSCHED h2
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have NIN : Task_in_time_slot ts slot_order tsk task_time_slot t = false := by
    rw [← sched_eq_in_slot job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN]; exact NSCHED
  rw [in_slot_false_iff] at NIN
  have PEN1 := pendingSt job_arrival job_cost sched j t PEN NSCHED
  rw [sched_eq_in_slot job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed (t + 1) PEN1, in_slot_false_iff]
  unfold to_next_slot at h2
  rw [fs_succ_lt task_time_slot slot_order ts tsk hc t (by omega')]; omega'

theorem duration_not_sched {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ t : time, pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      ∀ d : Nat, d < to_next_slot task_time_slot slot_order ts tsk t → scheduled_at sched j (t + d) = false ∧ pending job_arrival job_cost sched j (t + d) = true := by
  intro t PEN NSCHED d
  induction d with
  | zero => intro _; exact ⟨NSCHED, PEN⟩
  | succ d IH =>
    intro h
    obtain ⟨NS, PD⟩ := IH (by omega')
    rw [← Nat.add_assoc]
    refine ⟨S_t_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed (t + d) PD NS
      (lt_to_next_slot_LR task_time_slot slot_order ts tsk H_task_in_task_set H_valid_time_slot d 1 t (by omega')), ?_⟩
    exact pendingSt job_arrival job_cost sched j (t + d) PD NS

theorem pending_Nsched_sched {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ t : time, pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false → pending job_arrival job_cost sched j (t + to_next_slot task_time_slot slot_order ts tsk t) = true := by
  intro t PEN NSCHED
  have POSN := to_next_slot_pos task_time_slot slot_order ts tsk H_task_in_task_set H_valid_time_slot t
  obtain ⟨NS, PD⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED (to_next_slot task_time_slot slot_order ts tsk t - 1) (by omega')
  have := pendingSt job_arrival job_cost sched j _ PD NS
  rwa [Nat.add_assoc, Nat.sub_add_cancel POSN] at this

theorem at_next_start_of_slot_schedulabe {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ t : time, pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false → scheduled_at sched j (t + to_next_slot task_time_slot slot_order ts tsk t) = true := by
  intro t PEN NSCHED
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  rw [sched_eq_in_slot job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed _ (pending_Nsched_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED), in_slot_iff, fs_next task_time_slot slot_order ts tsk hc]
  exact hs

theorem formula_not_sched_St {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (t : time) (c : Nat), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      t + formula_rt task_time_slot slot_order ts tsk t (c + 1) = t + 1 + formula_rt task_time_slot slot_order ts tsk (t + 1) (c + 1) := by
  intro t c PEN NSCHED
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have hlt := fs_lt task_time_slot slot_order ts tsk hc t
  have NIN : Task_in_time_slot ts slot_order tsk task_time_slot t = false := by
    rw [← sched_eq_in_slot job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN]; exact NSCHED
  have NIN' := (in_slot_false_iff task_time_slot slot_order ts tsk t).mp NIN
  unfold formula_rt
  simp only [Nat.add_one_ne_zero, if_false, NIN, Bool.false_eq_true]
  unfold to_next_slot duration_to_finish_from_start_of_slot_with
  rcases Nat.lt_or_ge (from_start_of_slot task_time_slot slot_order ts tsk t + 1) (TDMA_cycle ts task_time_slot) with h1 | h1
  · have E := fs_succ_lt task_time_slot slot_order ts tsk hc t h1
    have NIN1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) = false :=
      (in_slot_false_iff task_time_slot slot_order ts tsk (t + 1)).mpr (by omega')
    simp only [NIN1, Bool.false_eq_true, if_false, E]
    omega'
  · have E := fs_succ_eq task_time_slot slot_order ts tsk hc t (by omega')
    have IN1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) = true :=
      (in_slot_iff task_time_slot slot_order ts tsk (t + 1)).mpr (by omega')
    simp only [IN1, if_true]
    simp only [to_end_of_slot, to_next_slot]
    simp only [E]
    split
    · next hcs =>
      rw [ceil_eq1 (c + 1) (task_time_slot tsk) (by omega') (by omega')]
      simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add]
      omega'
    · next hcs =>
      have hsuba := ceil_suba (c + 1) (task_time_slot tsk) hs (by omega')
      have hm := ceil_neq0 (c + 1 - (task_time_slot tsk - 0)) (task_time_slot tsk) (by omega') hs
      simp only [Nat.sub_zero] at hm ⊢
      rw [hsuba, Nat.add_sub_cancel]
      have := mul_pred_add (div_ceil (c + 1 - task_time_slot tsk) (task_time_slot tsk))
        (TDMA_cycle ts task_time_slot - task_time_slot tsk) hm
      omega'

theorem formula_sched_St {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (t : time) (c : Nat), scheduled_at sched j t = true → t + formula_rt task_time_slot slot_order ts tsk t (c + 1) = t + 1 + formula_rt task_time_slot slot_order ts tsk (t + 1) c := by
  intro t c SCHED
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have hlt := fs_lt task_time_slot slot_order ts tsk hc t
  have IN : Task_in_time_slot ts slot_order tsk task_time_slot t = true := by
    have := (TDMA_policy j t job_in_arr_seq).1 SCHED; rwa [H_job_task] at this
  have IN' := (in_slot_iff task_time_slot slot_order ts tsk t).mp IN
  unfold formula_rt
  simp only [Nat.add_one_ne_zero, if_false, IN, if_true]
  unfold to_end_of_slot to_next_slot duration_to_finish_from_start_of_slot_with
  rcases Nat.eq_zero_or_pos c with c0 | cpos
  · subst c0
    simp only [if_true]
    rw [if_pos (by omega')]
  · rw [if_neg (show ¬ c = 0 by omega')]
    rcases Nat.lt_or_ge (from_start_of_slot task_time_slot slot_order ts tsk t + 1) (TDMA_cycle ts task_time_slot) with h1 | h1
    · have E := fs_succ_lt task_time_slot slot_order ts tsk hc t h1
      rcases Nat.lt_or_ge (from_start_of_slot task_time_slot slot_order ts tsk t + 1) (task_time_slot tsk) with h2 | h2
      · have IN1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) = true :=
          (in_slot_iff task_time_slot slot_order ts tsk (t + 1)).mpr (by omega')
        simp only [IN1, if_true, E]
        by_cases hc1 : c + 1 ≤ task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk t
        · rw [if_pos hc1, if_pos (by omega')]; omega'
        · rw [if_neg hc1, if_neg (by omega'),
            show c - (task_time_slot tsk - (from_start_of_slot task_time_slot slot_order ts tsk t + 1)) = c + 1 - (task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk t) by omega']
          omega'
      · have NIN1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) = false :=
          (in_slot_false_iff task_time_slot slot_order ts tsk (t + 1)).mpr (by omega')
        simp only [NIN1, Bool.false_eq_true, if_false, E]
        rw [if_neg (by omega'), show c + 1 - (task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk t) = c by omega']
        omega'
    · have E := fs_succ_eq task_time_slot slot_order ts tsk hc t (by omega')
      have hseq : task_time_slot tsk = TDMA_cycle ts task_time_slot := by omega'
      have IN1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) = true :=
        (in_slot_iff task_time_slot slot_order ts tsk (t + 1)).mpr (by omega')
      simp only [IN1, if_true, E]
      rw [if_neg (by omega'), show c + 1 - (task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk t) = c by omega']
      have Z : TDMA_cycle ts task_time_slot - task_time_slot tsk = 0 := by omega'
      simp only [Z, Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
      split <;> omega'

theorem formula_not_sched_interval {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (t : time) (c : Nat), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      ∀ d : Nat, d < to_next_slot task_time_slot slot_order ts tsk t → t + formula_rt task_time_slot slot_order ts tsk t (c + 1) = t + d + formula_rt task_time_slot slot_order ts tsk (t + d) (c + 1) := by
  intro t c PEN NSCHED d
  induction d with
  | zero => intro _; simp
  | succ d IH =>
    intro h
    obtain ⟨NS, PD⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED d (by omega')
    rw [IH (by omega'), formula_not_sched_St job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed (t + d) c PD NS, Nat.add_assoc t d 1]

theorem formula_not_sched_to_next_slot {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (t : time) (c : Nat), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      t + formula_rt task_time_slot slot_order ts tsk t (c + 1) = t + to_next_slot task_time_slot slot_order ts tsk t + formula_rt task_time_slot slot_order ts tsk (t + to_next_slot task_time_slot slot_order ts tsk t) (c + 1) := by
  intro t c PEN NSCHED
  have POSN := to_next_slot_pos task_time_slot slot_order ts tsk H_task_in_task_set H_valid_time_slot t
  obtain ⟨NS, PD⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED (to_next_slot task_time_slot slot_order ts tsk t - 1) (by omega')
  rw [formula_not_sched_interval job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t c PEN NSCHED (to_next_slot task_time_slot slot_order ts tsk t - 1) (by omega'),
    formula_not_sched_St job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed _ c PD NS, Nat.add_assoc t _ 1, Nat.sub_add_cancel POSN]

theorem job_not_sched_to_cunsume_1unit {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (t : time) (c : Nat), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      t + formula_rt task_time_slot slot_order ts tsk t (c + 1) = (t + to_next_slot task_time_slot slot_order ts tsk t) + 1 + formula_rt task_time_slot slot_order ts tsk ((t + to_next_slot task_time_slot slot_order ts tsk t) + 1) c := by
  intro t c PEN NSCHED
  rw [formula_not_sched_to_next_slot job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t c PEN NSCHED,
    formula_sched_St job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed _ c (at_next_start_of_slot_schedulabe job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED)]

theorem end_time_predicate_not_sched_eq {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (d c : Nat) (t : time) (e : instant), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      end_time_predicate sched j t (c + 1) e → d < to_next_slot task_time_slot slot_order ts tsk t → end_time_predicate sched j (t + d) (c + 1) e := by
  intro d
  induction d with
  | zero => intro c t e _ _ H _; simpa using H
  | succ d IH =>
    intro c t e PEN NSCHED H h
    have H' := IH c t e PEN NSCHED H (by omega')
    obtain ⟨NS, _⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED d (by omega')
    rw [← Nat.add_assoc]
    exact end_time_predicate_not_sched j sched (t + d) c e (by rw [NS]; simp) H'

theorem end_time_predicate_not_sched_eq_rev {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (d c : Nat) (t : time) (e : instant), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      end_time_predicate sched j (t + d) (c + 1) e → d < to_next_slot task_time_slot slot_order ts tsk t → end_time_predicate sched j t (c + 1) e := by
  intro d
  induction d with
  | zero => intro c t e _ _ H _; simpa using H
  | succ d IH =>
    intro c t e PEN NSCHED H h
    obtain ⟨NS, _⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED d (by omega')
    apply IH c t e PEN NSCHED _ (by omega')
    rw [← Nat.add_assoc] at H
    exact end_time_predicate.S_C_not_sched _ _ _ (by rw [NS]; simp) H

theorem end_time_predicate_eq {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (t : time) (c : Nat) (e : instant), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false →
      (end_time_predicate sched j t (c + 1) e ↔ end_time_predicate sched j ((t + to_next_slot task_time_slot slot_order ts tsk t) + 1) c e) := by
  intro t c e PEN NSCHED
  have POSN := to_next_slot_pos task_time_slot slot_order ts tsk H_task_in_task_set H_valid_time_slot t
  have SCHEDn := at_next_start_of_slot_schedulabe job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED
  obtain ⟨NS, PD⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED (to_next_slot task_time_slot slot_order ts tsk t - 1) (by omega')
  have E : t + (to_next_slot task_time_slot slot_order ts tsk t - 1) + 1 = t + to_next_slot task_time_slot slot_order ts tsk t := by omega'
  constructor
  · intro H
    have H1 := end_time_predicate_not_sched_eq job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed (to_next_slot task_time_slot slot_order ts tsk t - 1) c t e PEN NSCHED H (by omega')
    have H2 := end_time_predicate_not_sched j sched _ c e (by rw [NS]; simp) H1
    rw [E] at H2
    exact end_time_predicate_sched j sched _ c e SCHEDn H2
  · intro H
    have H2 : end_time_predicate sched j (t + to_next_slot task_time_slot slot_order ts tsk t) (c + 1) e := end_time_predicate.S_C_sched _ _ _ SCHEDn H
    rw [← E] at H2
    have H1 := end_time_predicate.S_C_not_sched _ _ _ (by rw [NS]; simp) H2
    exact end_time_predicate_not_sched_eq_rev job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed (to_next_slot task_time_slot slot_order ts tsk t - 1) c t e PEN NSCHED H1 (by omega')

theorem service_is_zero_in_Nsched_duration {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (d : Nat) (t : time), pending job_arrival job_cost sched j t = true → scheduled_at sched j t = false → d ≤ to_next_slot task_time_slot slot_order ts tsk t →
      service sched j (t + d) = service sched j t := by
  intro d
  induction d with
  | zero => intro t _ _ _; rfl
  | succ d IH =>
    intro t PEN NSCHED h
    obtain ⟨NS, _⟩ := duration_not_sched job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN NSCHED d (by omega')
    rw [← Nat.add_assoc, service_step, IH t PEN NSCHED (by omega')]
    simp [service_at, NS]

/-- LEAN_HELPER: `completes_at_end_time_pre` with pendingness only required for a positive remaining cost. -/
private theorem completes_aux {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (c : Nat) (t : time), (0 < c → pending job_arrival job_cost sched j t = true) → service sched j t + c = job_cost j →
      end_time_predicate sched j t c (t + formula_rt task_time_slot slot_order ts tsk t c) := by
  intro c
  induction c with
  | zero =>
    intro t _ _
    have : formula_rt task_time_slot slot_order ts tsk t 0 = 0 := by unfold formula_rt; simp
    rw [this, Nat.add_zero]
    exact end_time_predicate.C0_ t
  | succ c IH =>
    intro t PENc SC
    have PEN := PENc (Nat.succ_pos c)
    have ARR := of_decide_eq_true (show has_arrived job_arrival j t = true by
      simp only [pending, Bool.and_eq_true] at PEN; exact PEN.1)
    cases hs : scheduled_at sched j t
    · rw [job_not_sched_to_cunsume_1unit job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t c PEN hs]
      rw [end_time_predicate_eq job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t c _ PEN hs]
      have SZ := service_is_zero_in_Nsched_duration job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed (to_next_slot task_time_slot slot_order ts tsk t) t PEN hs (Nat.le_refl _)
      have SCHn := at_next_start_of_slot_schedulabe job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t PEN hs
      have SN : service sched j ((t + to_next_slot task_time_slot slot_order ts tsk t) + 1) = service sched j t + 1 := by
        rw [service_step, SZ]; simp [service_at, SCHn]
      apply IH
      · intro cpos
        simp only [pending, has_arrived, completed_by, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨decide_eq_true (by omega'), decide_eq_false (by rw [SN]; omega')⟩
      · rw [SN]; omega'
    · rw [formula_sched_St job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed t c hs]
      apply end_time_predicate.S_C_sched _ _ _ hs
      have SN : service sched j (t + 1) = service sched j t + 1 := by
        rw [service_step]; simp [service_at, hs]
      apply IH
      · intro cpos
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega'⟩
        exact pendingSt_Sched job_arrival job_cost sched task_time_slot slot_order ts tsk H_task_in_task_set j H_valid_time_slot t c' PEN
          (by omega') hs
      · rw [SN]; omega'

theorem completes_at_end_time_pre {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j) (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    ∀ (c : Nat) (t : time), pending job_arrival job_cost sched j t = true → service sched j t + c = job_cost j →
      end_time_predicate sched j t c (t + formula_rt task_time_slot slot_order ts tsk t c) :=
  fun c t PEN SC => completes_aux job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed c t (fun _ => PEN) SC

theorem completes_at_end_time {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true) :
    completes_at job_arrival job_cost sched j
      (job_arrival j + job_response_time_tdma_in_at_most_one_job_is_pending job_arrival job_cost task_time_slot slot_order ts tsk j) := by
  unfold completes_at job_response_time_tdma_in_at_most_one_job_is_pending
  apply completes_at_end_time_pre job_arrival job_cost job_task arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed
  · exact pendingArrival task_cost task_deadline job_arrival job_cost job_deadline job_task sched
      H_jobs_must_arrive_to_execute j H_valid_job
  · have Z := cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0
      (job_arrival j) (Nat.le_refl _)
    unfold service service_during; rw [Z, Nat.zero_add]

def WCRT_formula (cycle s wcet : Nat) : Nat :=
  div_ceil wcet s * (cycle - s) + wcet

def WCRT {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost : sporadic_task → time) (task_time_slot : TDMA_slot sporadic_task) (ts : set sporadic_task)
    (tsk : sporadic_task) : Nat :=
  WCRT_formula (TDMA_cycle ts task_time_slot) (task_time_slot tsk) (task_cost tsk)

theorem response_time_le_WCRT {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true)
    (H_job_cost_le_task_cost : job_cost_le_task_cost task_cost job_cost job_task j = true) :
    job_response_time_tdma_in_at_most_one_job_is_pending job_arrival job_cost task_time_slot slot_order ts tsk j ≤
      WCRT task_cost task_time_slot ts tsk := by
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have cost_pos := H_valid_job.1.1
  simp only [job_cost_positive, decide_eq_true_eq] at cost_pos
  have CLE := H_job_cost_le_task_cost
  simp only [job_cost_le_task_cost, decide_eq_true_eq, H_job_task] at CLE
  have hlt := fs_lt task_time_slot slot_order ts tsk hc (job_arrival j)
  have hW := ceil_neq0 (task_cost tsk) (task_time_slot tsk) (by omega') hs
  unfold job_response_time_tdma_in_at_most_one_job_is_pending WCRT WCRT_formula formula_rt
  rw [if_neg (by omega')]
  unfold to_end_of_slot to_next_slot duration_to_finish_from_start_of_slot_with
  split
  · next INS =>
    have INS' := (in_slot_iff task_time_slot slot_order ts tsk _).mp INS
    split
    · next hle =>
      calc job_cost j ≤ task_cost tsk := CLE
        _ ≤ _ := Nat.le_add_left _ _
    · next hle =>
      have hm := ceil_neq0 (job_cost j - (task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk (job_arrival j))) (task_time_slot tsk)
        (by omega') hs
      have hmono := leq_divceil2r (task_time_slot tsk) (job_cost j - (task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk (job_arrival j)))
        (task_cost tsk) hs (by omega')
      have E := mul_pred_add (div_ceil (job_cost j - (task_time_slot tsk - from_start_of_slot task_time_slot slot_order ts tsk (job_arrival j))) (task_time_slot tsk))
        (TDMA_cycle ts task_time_slot - task_time_slot tsk) hm
      have M := Nat.mul_le_mul_right (TDMA_cycle ts task_time_slot - task_time_slot tsk) hmono
      omega'
  · next NINS =>
    have NINS' := (in_slot_false_iff task_time_slot slot_order ts tsk _).mp (by simpa using NINS)
    have hm := ceil_neq0 (job_cost j) (task_time_slot tsk) (by omega') hs
    have hmono := leq_divceil2r (task_time_slot tsk) (job_cost j) (task_cost tsk) hs CLE
    have E := mul_pred_add (div_ceil (job_cost j) (task_time_slot tsk)) (TDMA_cycle ts task_time_slot - task_time_slot tsk) hm
    have M := Nat.mul_le_mul_right (TDMA_cycle ts task_time_slot - task_time_slot tsk) hmono
    omega'

theorem exists_WCRT {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true)
    (H_job_cost_le_task_cost : job_cost_le_task_cost task_cost job_cost job_task j = true) :
    job_cost j = task_cost tsk ∧ from_start_of_slot task_time_slot slot_order ts tsk (job_arrival j) = task_time_slot tsk →
      job_response_time_tdma_in_at_most_one_job_is_pending job_arrival job_cost task_time_slot slot_order ts tsk j =
        WCRT task_cost task_time_slot ts tsk := by
  intro ⟨COST_WCET, EXISTS⟩
  have hc : 0 < TDMA_cycle ts task_time_slot := TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
  have hs : 0 < task_time_slot tsk := by simpa [is_valid_time_slot] using H_valid_time_slot
  have hsc : task_time_slot tsk ≤ TDMA_cycle ts task_time_slot := TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
  have cost_pos := H_valid_job.1.1
  simp only [job_cost_positive, decide_eq_true_eq] at cost_pos
  have NINS : Task_in_time_slot ts slot_order tsk task_time_slot (job_arrival j) = false :=
    (in_slot_false_iff task_time_slot slot_order ts tsk _).mpr (by omega')
  unfold job_response_time_tdma_in_at_most_one_job_is_pending WCRT WCRT_formula formula_rt
  rw [if_neg (by omega'), NINS]
  simp only [Bool.false_eq_true, if_false]
  unfold to_next_slot duration_to_finish_from_start_of_slot_with
  rw [EXISTS, COST_WCET]
  have hm := ceil_neq0 (task_cost tsk) (task_time_slot tsk) (by omega') hs
  have E := mul_pred_add (div_ceil (task_cost tsk) (task_time_slot tsk)) (TDMA_cycle ts task_time_slot - task_time_slot tsk) hm
  omega'

theorem job_completed_by_WCRT {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task) (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts) (j : Job) (H_job_task : job_task j = tsk)
    (job_in_arr_seq : arrives_in arr_seq j)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (all_previous_jobs_of_same_task_completed : ∀ j_other, arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true)
    (H_job_cost_le_task_cost : job_cost_le_task_cost task_cost job_cost job_task j = true) :
    completed_by job_cost sched j (job_arrival j + WCRT task_cost task_time_slot ts tsk) = true := by
  have LE := response_time_le_WCRT task_cost task_deadline job_arrival job_cost job_deadline job_task arr_seq sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq
    H_valid_job H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed H_job_cost_le_task_cost
  have C := completed_by_end_time job_arrival job_cost j sched H_jobs_must_arrive_to_execute _
    (completes_at_end_time task_cost task_deadline job_arrival job_cost job_deadline job_task arr_seq sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j H_job_task job_in_arr_seq
      H_valid_job H_valid_time_slot TDMA_policy all_previous_jobs_of_same_task_completed)
  exact completion_monotonic job_cost sched j _ _ (Nat.add_le_add_left LE _) C

end Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA
