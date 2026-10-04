import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Util.Sum
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup
import Prosa.Classic.Util.Counting
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
General facts used by several case-study proofs, proved from the classic Lean Prosa.
-/

/-- `omega` after unfolding the classic `time`/`instant`/`duration` aliases (which `omega` does not see
through). -/
macro "tomega" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

namespace Solutions.Support.Common

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime

universe u v

/-- A response-time bound stays a bound when it is enlarged. -/
theorem rtb_mono {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    {job_arrival job_cost : Job → time} {job_task : Job → sporadic_task} {arr_seq : arrival_sequence Job}
    {num_cpus : Nat} {sched : schedule Job num_cpus} {tsk : sporadic_task} {R R' : time} (hR : R ≤ R')
    (H : is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R' := by
  intro j hj ht
  exact completion_monotonic job_cost sched j _ _ (Nat.add_le_add_left hR _) (H j hj ht)

end Solutions.Support.Common

namespace Solutions.Support.Common

open Prosa.Util.Sum (sumSeq)

/-- A sum of terms each at most one is at most the length of the list. -/
theorem sumSeq_le_length_of_le_one {I : Type _} (L : List I) (F : I → Nat) (h : ∀ x ∈ L, F x ≤ 1) :
    sumSeq L F ≤ L.length := by
  unfold sumSeq
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := h a (List.mem_cons_self ..)
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega

/-- Summing ones counts the elements. -/
theorem sumSeq_one {I : Type _} (L : List I) : sumSeq L (fun _ => 1) = L.length := by
  unfold sumSeq; induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

end Solutions.Support.Common

namespace Solutions.Support.Common

open Prosa.Util.Sum (sumSeq)

theorem sumSeq_perm {I : Type _} {L L' : List I} (F : I → Nat) (h : L.Perm L') : sumSeq L F = sumSeq L' F := by
  unfold sumSeq; exact (h.map F).sum_eq

theorem sumSeq_append {I : Type _} (A B : List I) (F : I → Nat) : sumSeq (A ++ B) F = sumSeq A F + sumSeq B F := by
  unfold sumSeq; simp

theorem sumSeq_le_sumSeq {I : Type _} (L : List I) (F G : I → Nat) (h : ∀ x ∈ L, F x ≤ G x) :
    sumSeq L F ≤ sumSeq L G := by
  unfold sumSeq
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- A duplicate-free list is a permutation of any prefix of a permutation of it followed by its elements outside
that prefix. -/
theorem perm_take_append_filter {α : Type _} [DecidableEq α] {L S : List α} (hS : S.Perm L) (hnd : L.Nodup)
    (k : Nat) : L.Perm (S.take k ++ L.filter (fun p => !decide (p ∈ S.take k))) := by
  have hSnd : S.Nodup := hS.nodup_iff.mpr hnd
  have hdisj := List.disjoint_take_drop hSnd (Nat.le_refl k)
  have h1 : S.filter (fun p => !decide (p ∈ S.take k)) = S.drop k := by
    have hsplit : S.filter (fun p => !decide (p ∈ S.take k)) =
        (S.take k).filter (fun p => !decide (p ∈ S.take k)) ++
          (S.drop k).filter (fun p => !decide (p ∈ S.take k)) := by
      rw [← List.filter_append, List.take_append_drop]
    rw [hsplit]
    have ha : (S.take k).filter (fun p => !decide (p ∈ S.take k)) = [] := by
      rw [List.filter_eq_nil_iff]; intro p hp; simp [hp]
    have hb : (S.drop k).filter (fun p => !decide (p ∈ S.take k)) = S.drop k := by
      rw [List.filter_eq_self]; intro p hp
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact fun h => hdisj h hp
    rw [ha, hb, List.nil_append]
  have h2 : (L.filter (fun p => !decide (p ∈ S.take k))).Perm (S.drop k) := by
    rw [← h1]; exact (hS.filter _).symm
  have h3 : S.Perm (S.take k ++ L.filter (fun p => !decide (p ∈ S.take k))) := by
    conv_lhs => rw [← List.take_append_drop k S]
    exact List.Perm.append_left _ h2.symm
  exact hS.symm.trans h3

end Solutions.Support.Common

/-! ### Busy windows under global fixed-priority scheduling -/

namespace Solutions.Support.Common

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Util.Counting

universe u v

/-- At most `num_cpus` tasks of a task set are scheduled at `t` (as the classic private
`count_task_is_scheduled_le`). -/
theorem count_task_is_scheduled_le {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (ts : taskset_of sporadic_task)
    (t : time) (P : sporadic_task → Bool)
    (hP : ∀ x, P x = true → task_is_scheduled job_task sched x t = true) :
    ts.val.countP P ≤ num_cpus := by
  apply Nat.le_trans (sub_in_count _ ts.val P (fun x => task_is_scheduled job_task sched x t)
    (fun x _ h => hP x h))
  apply count_exists _ ts.val num_cpus
    (fun x cpu => task_scheduled_on job_task sched x cpu t) ts.nodup
  intro cpu x1 x2 S1 S2
  unfold task_scheduled_on at S1 S2
  cases hs : sched cpu t with
  | none => simp [hs] at S1
  | some k =>
      simp only [hs, decide_eq_true_eq] at S1 S2
      rw [← S1, ← S2]

/-- Under sequential tasks, two distinct jobs of the same task are never scheduled at the same
time. -/
theorem same_task_scheduled_eq {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (ts : taskset_of sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (t : time) (j1 j2 : Job) (h1 : scheduled sched j1 t = true) (h2 : scheduled sched j2 t = true)
    (hsame : job_task j1 = job_task j2) : j1 = j2 := by
  by_contra hne
  have A1 := H_jobs_come_from_arrival_sequence j1 t h1
  have A2 := H_jobs_come_from_arrival_sequence j2 t h2
  have hper : 0 < task_period (job_task j1) := by
    have := (H_valid_task_parameters _ (H_all_jobs_from_taskset j1 A1)).2.1
    simpa [task_period_positive] using this
  -- the earlier job is completed while still scheduled
  have key : ∀ a b : Job, a ≠ b → arrives_in arr_seq a → arrives_in arr_seq b →
      job_task a = job_task b → 0 < task_period (job_task a) → job_arrival a ≤ job_arrival b →
      scheduled sched a t = true → scheduled sched b t = true → False := by
    intro a b hab Aa Ab hs hp hle sa sb
    have SPO := H_sporadic_tasks a b hab Aa Ab hs hle
    obtain ⟨cpu, hcpu⟩ : ∃ cpu, scheduled_on sched b cpu t = true := by
      simpa [scheduled, List.any_eq_true] using sb
    have hc := H_sequential_tasks a b t cpu Aa Ab hs (by tomega) hcpu
    have hpend := scheduled_implies_pending job_arrival job_cost sched a
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t sa
    simp [pending, hc] at hpend
  rcases Nat.le_total (job_arrival j1) (job_arrival j2) with h | h
  · exact key j1 j2 hne A1 A2 hsame hper h h1 h2
  · exact key j2 j1 (Ne.symm hne) A2 A1 hsame.symm (hsame ▸ hper) h h2 h1

/-- If a pending job of a higher-priority task is not scheduled at `t`, then all processors are
busy with jobs of distinct higher-priority tasks: the number of higher-priority tasks scheduled at
`t` is `num_cpus`.  Contrapositive form: at an instant that is not "hp-busy", every pending job of
a higher-priority task is scheduled. -/
theorem scheduled_of_pending_hp_not_busy {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (ts : taskset_of sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (tsk : sporadic_task) (tsk_in_ts : tsk ∈ ts) (j0 : Job) (H_j0_arrives : arrives_in arr_seq j0)
    (H_hp : higher_priority_task higher_eq_priority tsk (job_task j0) = true) (t : time)
    (H_pending : pending job_arrival job_cost sched j0 t = true)
    (H_not_busy : ts.val.countP (fun k => task_is_scheduled job_task sched k t &&
      higher_priority_task higher_eq_priority tsk k) ≠ num_cpus) :
    scheduled sched j0 t = true := by
  by_contra hns
  have hback : backlogged job_arrival job_cost sched j0 t = true := by
    simp only [Bool.not_eq_true] at hns
    simp [backlogged, H_pending, hns]
  apply H_not_busy
  set P := fun k => task_is_scheduled job_task sched k t &&
    higher_priority_task higher_eq_priority tsk k with hP
  apply Nat.le_antisymm
  · apply count_task_is_scheduled_le job_task sched ts t
    intro x hx
    simp only [hP, Bool.and_eq_true] at hx
    exact hx.1
  · have hlen := (work_conserving_eq_work_conserving_count job_arrival job_cost arr_seq sched).mp
      H_work_conserving j0 t H_j0_arrives hback
    have hmem : ∀ j', j' ∈ jobs_scheduled_at sched t ↔ scheduled sched j' t = true := by
      intro j'; rw [← mem_scheduled_jobs_eq_scheduled, decide_eq_true_iff]
    have hhp0 := H_hp
    simp only [higher_priority_task, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hhp0
    have hj0ts := H_all_jobs_from_taskset j0 H_j0_arrives
    rw [← hlen, ← List.length_map (f := job_task)]
    have hnd : ((jobs_scheduled_at sched t).map job_task).Nodup := by
      apply List.Nodup.map_on _ (scheduled_jobs_uniq sched H_sequential_jobs t)
      intro j1 S1 j2 S2 hs
      exact same_task_scheduled_eq task_cost task_period task_deadline job_arrival job_cost job_task
        arr_seq ts sched H_sporadic_tasks H_valid_task_parameters H_all_jobs_from_taskset
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_tasks t j1 j2 ((hmem j1).mp S1)
        ((hmem j2).mp S2) hs
    have hall : ∀ k ∈ (jobs_scheduled_at sched t).map job_task, P k = true ∧ k ∈ ts.val := by
      intro k hk
      obtain ⟨j', S', rfl⟩ := List.mem_map.mp hk
      rw [hmem] at S'
      have A' := H_jobs_come_from_arrival_sequence j' t S'
      have hep' := H_respects_FP_policy j0 j' t H_j0_arrives hback S'
      have hep'' : higher_eq_priority (job_task j') tsk = true :=
        H_priority_transitive _ _ _ hep' hhp0.1
      have hts : task_is_scheduled job_task sched (job_task j') t = true := by
        obtain ⟨cpu, hcpu⟩ : ∃ cpu, sched cpu t = some j' := by
          simpa [scheduled, scheduled_on, List.any_eq_true] using S'
        simp only [task_is_scheduled, List.any_eq_true, List.mem_finRange, true_and]
        exact ⟨cpu, by simp [task_scheduled_on, hcpu]⟩
      have hne : job_task j' ≠ tsk := by
        intro heq
        rw [heq] at hep'
        exact hhp0.2 (H_priority_antisymmetric _ _ hj0ts tsk_in_ts hhp0.1 hep')
      exact ⟨by simp [hP, higher_priority_task, hts, hep'', hne], H_all_jobs_from_taskset j' A'⟩
    calc ((jobs_scheduled_at sched t).map job_task).length
        = ((jobs_scheduled_at sched t).map job_task).countP P := by
          rw [List.countP_eq_length_filter, List.filter_eq_self.mpr (fun k hk => (hall k hk).1)]
      _ ≤ ts.val.countP P := count_sub_uniqr _ _ _ P hnd (fun k hk => (hall k hk).2)

/-- A job scheduled at `t` has received service by `t + 1`. -/
theorem service_pos_of_scheduled {Job : Type v} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) (h : scheduled sched j t = true) :
    1 ≤ service sched j (t + 1) := by
  have h0 := not_scheduled_no_service sched j t
  rw [h] at h0
  have hne : service_at sched j t ≠ 0 := by simpa using h0.symm
  have := Finset.single_le_sum (f := fun x => service_at sched j x)
    (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨Nat.zero_le t, Nat.lt_add_one t⟩)
  unfold service
  tomega

/-- Carry-in jobs at the start `t0` of a maximal hp-busy window are scheduled at `t0 - 1`. -/
theorem carry_in_job_scheduled {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (ts : taskset_of sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (tsk : sporadic_task) (tsk_in_ts : tsk ∈ ts) (t0 : time)
    (H_left : t0 = 0 ∨ ¬ ts.val.countP (fun k => task_is_scheduled job_task sched k (t0 - 1) &&
      higher_priority_task higher_eq_priority tsk k) = num_cpus)
    (j0 : Job) (H_j0_arrives : arrives_in arr_seq j0)
    (H_hp : higher_priority_task higher_eq_priority tsk (job_task j0) = true)
    (H_before : job_arrival j0 < t0) (H_not_completed : (!completed job_cost sched j0 t0) = true) :
    scheduled sched j0 (t0 - 1) = true := by
  rcases H_left with h0 | hnb
  · tomega
  apply scheduled_of_pending_hp_not_busy task_cost task_period task_deadline job_arrival job_cost
    job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks H_valid_task_parameters
    H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_transitive
    H_priority_antisymmetric H_work_conserving H_respects_FP_policy H_sequential_tasks tsk tsk_in_ts
    j0 H_j0_arrives H_hp (t0 - 1) _ hnb
  have hnc : completed job_cost sched j0 (t0 - 1) = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have := completion_monotonic job_cost sched j0 _ t0 (Nat.sub_le _ _) hc
    simp [this] at H_not_completed
  simp [pending, has_arrived, hnc]
  tomega

/-- Summing Boolean indicators counts. -/
theorem sumSeq_toNat_eq_countP {K : Type _} (L : List K) (f : K → Bool) :
    Prosa.Util.Sum.sumSeq L (fun k => (f k).toNat) = L.countP f := by
  unfold Prosa.Util.Sum.sumSeq
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases f a <;> simp [Nat.add_comm]

/-- If, whenever `j` is backlogged in `[a, b)`, every processor runs a job of a task in the duplicate-free
list `L`, then the interferences of the tasks of `L` on `j` add up to `num_cpus` times its total
interference. -/
theorem sum_task_interference_eq {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (L : List sporadic_task) (hnd : L.Nodup) (j : Job) (a b : time)
    (hall : ∀ t, a ≤ t → t < b → backlogged job_arrival job_cost sched j t = true →
      ∀ cpu, ∃ j', sched cpu t = some j' ∧ job_task j' ∈ L) :
    Prosa.Util.Sum.sumSeq L (fun k =>
        Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.task_interference
          job_arrival job_cost job_task sched j k a b) =
      num_cpus *
        Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.total_interference
          job_arrival job_cost sched j a b := by
  unfold Prosa.Util.Sum.sumSeq
    Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.task_interference
    Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.total_interference
  rw [← List.sum_toFinset _ hnd, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  rw [Finset.sum_comm]
  by_cases hb : backlogged job_arrival job_cost sched j t = true
  · have hone : ∀ cpu : Fin num_cpus, ∑ k ∈ L.toFinset,
        (backlogged job_arrival job_cost sched j t &&
          task_scheduled_on job_task sched k cpu t).toNat = 1 := by
      intro cpu
      obtain ⟨j', hs, hin⟩ := hall t ht.1 ht.2 hb cpu
      simp only [hb, Bool.true_and, task_scheduled_on, hs]
      rw [Finset.sum_eq_single (job_task j')]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · intro h; exact absurd (List.mem_toFinset.mpr hin) h
    rw [Finset.sum_congr rfl (fun cpu _ => hone cpu)]
    simp [hb]
  · simp only [Bool.not_eq_true] at hb
    simp [hb]

/-- If every element is at most `X`, the elements sum to `m X` and `c ≤ X`, then the elements
truncated at `c` sum to at least `m c`. -/
theorem sum_min_ge {α : Type _} (L : List α) (f : α → Nat) (m X c : Nat)
    (hsum : Prosa.Util.Sum.sumSeq L f = m * X) (hle : ∀ x ∈ L, f x ≤ X) (hc : c ≤ X) :
    m * c ≤ Prosa.Util.Sum.sumSeq L (fun x => min (f x) c) := by
  have hpt : ∀ x ∈ L, c * f x ≤ X * min (f x) c := by
    intro x hx
    rcases Nat.le_total (f x) c with h | h
    · rw [min_eq_left h]; exact Nat.mul_le_mul_right _ hc
    · rw [min_eq_right h, Nat.mul_comm X]; exact Nat.mul_le_mul_left _ (hle x hx)
  have hS := sumSeq_le_sumSeq L (fun x => c * f x) (fun x => X * min (f x) c) hpt
  unfold Prosa.Util.Sum.sumSeq at hS hsum ⊢
  rw [List.sum_map_mul_left, List.sum_map_mul_left, hsum] at hS
  rcases Nat.eq_zero_or_pos X with h0 | hX
  · subst h0; have : c = 0 := by omega
    subst this; simp
  · apply Nat.le_of_mul_le_mul_left _ hX
    calc X * (m * c) = c * (m * X) := by rw [Nat.mul_comm X, Nat.mul_comm m c, Nat.mul_assoc]
      _ ≤ _ := hS

/-- Under sequential tasks, a task interferes with a job at most as much as the job's total
interference: at each instant at most one processor runs a job of that task. -/
theorem task_interference_le_total {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (ts : taskset_of sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (j : Job) (k : sporadic_task) (a b : time) :
    Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.task_interference
        job_arrival job_cost job_task sched j k a b ≤
      Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.total_interference
        job_arrival job_cost sched j a b := by
  unfold Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.task_interference
    Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.total_interference
  apply Finset.sum_le_sum
  intro t _
  cases hb : backlogged job_arrival job_cost sched j t
  · simp
  · simp only [Bool.true_and, Bool.toNat_true]
    have hsched : ∀ cpu j', sched cpu t = some j' → scheduled sched j' t = true := by
      intro cpu j' h
      simp only [scheduled, List.any_eq_true, List.mem_finRange, true_and, scheduled_on,
        decide_eq_true_eq]
      exact ⟨cpu, h⟩
    calc ∑ cpu : Fin num_cpus, (task_scheduled_on job_task sched k cpu t).toNat
        = (Finset.univ.filter (fun cpu => task_scheduled_on job_task sched k cpu t = true)).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl; intro cpu _; cases task_scheduled_on job_task sched k cpu t <;> rfl
      _ ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro c1 h1 c2 h2
          rw [Finset.mem_filter] at h1 h2
          replace h1 := h1.2
          replace h2 := h2.2
          unfold task_scheduled_on at h1 h2
          cases hs1 : sched c1 t with
          | none => rw [hs1] at h1; exact absurd h1 (by simp)
          | some j1 =>
            cases hs2 : sched c2 t with
            | none => rw [hs2] at h2; exact absurd h2 (by simp)
            | some j2 =>
              rw [hs1] at h1; rw [hs2] at h2
              simp only [decide_eq_true_eq] at h1 h2
              have := same_task_scheduled_eq task_cost task_period task_deadline job_arrival job_cost
                job_task arr_seq ts sched H_sporadic_tasks H_valid_task_parameters
                H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_tasks t
                j1 j2 (hsched c1 j1 hs1) (hsched c2 j2 hs2) (h1.trans h2.symm)
              subst this
              exact H_sequential_jobs j1 t c1 c2 hs1 hs2

open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference in
/-- A job that is not complete `R ≥ c_j` time units after its arrival is backlogged for at least
`R - c_j + 1` of them. -/
theorem too_much_interference_job {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) (R : time) (hR : job_cost j ≤ R)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true) :
    R - job_cost j + 1 ≤ total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) := by
  have NOTCOMP := H_j_not_completed
  simp only [completed, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NOTCOMP
  have hsvc : service sched j (job_arrival j + R) =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t :=
    service_before_arrival_eq_service_during job_arrival sched j H_jobs_must_arrive_to_execute 0 R
      (Nat.zero_le _)
  have hcover : R ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      ((backlogged job_arrival job_cost sched j t).toNat + service_at sched j t) := by
    calc R = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        cases hb : backlogged job_arrival job_cost sched j t
        · simp only [Bool.toNat_false, Nat.zero_add]
          have hpend : pending job_arrival job_cost sched j t = true := by
            simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true']
            refine ⟨ht.1, ?_⟩
            cases hc : completed job_cost sched j t
            · rfl
            · have := completion_monotonic job_cost sched j t (job_arrival j + R)
                (Nat.le_of_lt ht.2) hc
              simp only [completed, decide_eq_true_eq] at this
              tomega
          simp only [backlogged, hpend, Bool.true_and, Bool.not_eq_false'] at hb
          have := not_scheduled_no_service sched j t
          rw [hb] at this
          have hne : service_at sched j t ≠ 0 := by
            intro h0; rw [h0] at this; simp at this
          tomega
        · simp
  unfold total_interference
  rw [Finset.sum_add_distrib] at hcover
  rw [hsvc] at NOTCOMP
  tomega

open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference in
/-- A job that is complete `R` time units after its arrival is backlogged for at most `R - c_j`
of them. -/
theorem low_interference_of_completed {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) (R : time) (hcomp : completed job_cost sched j (job_arrival j + R) = true) :
    total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) ≤ R - job_cost j := by
  simp only [completed, decide_eq_true_eq] at hcomp
  have hsvc : service sched j (job_arrival j + R) =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t :=
    service_before_arrival_eq_service_during job_arrival sched j H_jobs_must_arrive_to_execute 0 R
      (Nat.zero_le _)
  have hpt : ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      ((backlogged job_arrival job_cost sched j t).toNat + service_at sched j t) ≤ R := by
    calc _ ≤ ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), 1 := by
          apply Finset.sum_le_sum
          intro t _
          cases hb : backlogged job_arrival job_cost sched j t
          · simpa using service_at_most_one sched j H_sequential_jobs t
          · have h0 : service_at sched j t = 0 := by
              simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at hb
              have := not_scheduled_no_service sched j t
              rw [hb.2] at this
              simpa using this.symm
            rw [h0]; simp
      _ = R := by simp
  unfold total_interference
  rw [Finset.sum_add_distrib] at hpt
  rw [hsvc] at hcomp
  tomega

theorem sumSeq_mul_left {α : Type _} (L : List α) (f : α → Nat) (c : Nat) :
    Prosa.Util.Sum.sumSeq L (fun x => c * f x) = c * Prosa.Util.Sum.sumSeq L f := by
  unfold Prosa.Util.Sum.sumSeq; rw [List.sum_map_mul_left]

end Solutions.Support.Common
