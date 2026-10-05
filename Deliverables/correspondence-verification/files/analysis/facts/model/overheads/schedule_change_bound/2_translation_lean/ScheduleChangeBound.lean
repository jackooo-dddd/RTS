-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/overheads/schedule_change_bound.v

import Prosa.Model.Task.Arrival.Curves
import Prosa.Analysis.Facts.CompletesAt
import Prosa.Analysis.Facts.Model.Overheads.PriorityBump
import Prosa.Analysis.Facts.Model.Overheads.ScheduleChange
import Prosa.Analysis.Facts.Model.ArrivalCurves

namespace Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Readiness.Basic
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Overheads
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.Overheads.PriorityBump
open Prosa.Analysis.Definitions.Overheads.ScheduleChange
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Model.Preemption
open Prosa.Analysis.Facts.Priority.Sequential
open Prosa.Analysis.Facts.BusyInterval.HepAtPt
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Analysis.Facts.CompletesAt
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Overheads.Schedule
open Prosa.Analysis.Facts.Model.Overheads.PriorityBump
open Prosa.Util.List
open Prosa.Util.Sum

/-! Upper bounds on the number of schedule changes within a busy-interval prefix of an explicit-overhead
uniprocessor schedule, under JLFP, FP and FIFO scheduling. Binders follow the elaborated source types. The
source's section-local `basic_ready_instance` (implicit in the elaborated `valid_schedule`, `work_conserving` and
`respects_*_policy_at_preemption_point`) is the accepted Lean definition of the same name, passed explicitly; the
policy coercions (`JLFP_to_JLDP`, `FP_to_JLFP`) are the accepted ones. Representation: a Boolean in `Prop`
position is `= true`; `t1.+1` is `t1 + 1`; `\sum_(tsk <- ts) F tsk` is `sumSeq ts F` and a filtered sum is
`sumFiltered`.

The proof counts the instants of `[t1 + 1, t)`: every schedule change is a priority bump or the completion of
a job, a completion of a lower-priority job is itself a priority bump, and every higher-or-equal-priority job
arriving in `[t1, t)` accounts for at most one bump (it is the job scheduled at the bump) and at most one
completion. -/

/-! ### Counting over lists (LEAN_HELPER) -/

private theorem scb_countP_le_one {α : Type _} (p : α → Bool) :
    ∀ L : List α, L.Nodup → (∀ a ∈ L, ∀ b ∈ L, p a = true → p b = true → a = b) → L.countP p ≤ 1
  | [], _, _ => by simp
  | a :: L, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    by_cases hpa : p a = true
    · have h0 : L.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro b hb hpb
        apply hnd.1
        rw [h a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hpa hpb]
        exact hb
      simp [h0, hpa]
    · have := scb_countP_le_one p L hnd.2
        (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      simp [hpa]; omega

private theorem scb_countP_sum {β : Type _} (p : β → Bool) :
    ∀ A : List β, A.countP p = (A.map fun b => if p b = true then 1 else 0).sum
  | [] => by simp
  | b :: A => by
    rw [List.countP_cons, List.map_cons, List.sum_cons, scb_countP_sum p A]
    by_cases h : p b = true <;> simp [h] <;> omega

private theorem scb_sum_map_add {β : Type _} (f g : β → Nat) :
    ∀ A : List β, (A.map fun b => f b + g b).sum = (A.map f).sum + (A.map g).sum
  | [] => by simp
  | b :: A => by simp only [List.map_cons, List.sum_cons, scb_sum_map_add f g A]; omega

private theorem scb_double_count {α β : Type _} (q : α → β → Bool) (A : List β) :
    ∀ L : List α, (L.map fun a => A.countP (q a)).sum = (A.map fun b => L.countP (fun a => q a b)).sum
  | [] => by simp
  | a :: L => by
    rw [List.map_cons, List.sum_cons, scb_double_count q A L]
    have : (A.map fun b => (a :: L).countP (fun x => q x b)) =
        (A.map fun b => L.countP (fun x => q x b) + if q a b = true then 1 else 0) := by
      apply List.map_congr_left
      intro b _
      rw [List.countP_cons]
    rw [this, scb_sum_map_add, scb_countP_sum (q a) A]
    omega

private theorem scb_sum_le {α : Type _} (f g : α → Nat) :
    ∀ L : List α, (∀ a ∈ L, f a ≤ g a) → (L.map f).sum ≤ (L.map g).sum
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := scb_sum_le f g L (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

/-- LEAN_HELPER: if every instant satisfying `p` has a witness in `A` related by `q`, and every element of `A` is
related to at most one instant, then at most `|A|` instants satisfy `p`. -/
private theorem scb_count_le {α β : Type _} (L : List α) (A : List β) (p : α → Bool) (q : α → β → Bool)
    (hw : ∀ a ∈ L, p a = true → ∃ b ∈ A, q a b = true)
    (hu : ∀ b ∈ A, L.countP (fun a => q a b) ≤ 1) : L.countP p ≤ A.length := by
  calc L.countP p = (L.map fun a => if p a = true then 1 else 0).sum := scb_countP_sum p L
    _ ≤ (L.map fun a => A.countP (q a)).sum := by
        apply scb_sum_le
        intro a ha
        by_cases hp : p a = true
        · obtain ⟨b, hb, hq⟩ := hw a ha hp
          have : 0 < A.countP (q a) := List.countP_pos_iff.2 ⟨b, hb, hq⟩
          rw [if_pos hp]; exact this
        · simp [hp]
    _ = (A.map fun b => L.countP (fun a => q a b)).sum := scb_double_count q A L
    _ ≤ (A.map fun _ => 1).sum := scb_sum_le _ _ A hu
    _ = A.length := by simp

private theorem scb_countP_or_le {α : Type _} (p q : α → Bool) :
    ∀ L : List α, L.countP (fun a => p a || q a) ≤ L.countP p + L.countP q
  | [] => by simp
  | a :: L => by
    have := scb_countP_or_le p q L
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

private theorem scb_mem_index_iota {a b t : Nat} : t ∈ index_iota a b ↔ a ≤ t ∧ t < b := by
  simp only [index_iota, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨t - a, by omega, by omega⟩

private theorem scb_nodup_index_iota (a b : Nat) : (index_iota a b).Nodup := by
  unfold index_iota
  exact List.nodup_range' ..

/-! ### The busy-interval-prefix setting (LEAN_HELPER) -/

section Setting

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job] [JobPreemptable Job]

/-- The hypotheses of the source's helper section, bundled. -/
private structure ScbHyps (JLFP : JLFP_policy Job) (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (j : Job) (t1 t2 : instant) : Prop where
  refl : reflexive_job_priorities JLFP
  trans : transitive_job_priorities JLFP
  va : valid_arrival_sequence arr_seq
  vs : @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq
  wc : @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job)
    basic_ready_instance arr_seq sched
  nsp : @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := JLFP)) (processor_state Job) sched
  resp : @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance
    arr_seq sched JLFP
  vpm : valid_preemption_model arr_seq sched
  arr : arrives_in arr_seq j
  pos : job_cost_positive j = true
  bip : busy_interval_prefix arr_seq sched j t1 t2

variable {JLFP : JLFP_policy Job} {arr_seq : arrival_sequence Job} {sched : schedule (processor_state Job)}
  {j : Job} {t1 t2 : instant}

/-- Some job of the arrivals up to `t` completes at `t`. -/
private noncomputable def scb_comp (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job))
    (t : instant) : Bool :=
  (arrivals_up_to arr_seq t).any (fun jc => completes_at sched jc t)

private theorem scb_pending (H : ScbHyps JLFP arr_seq sched j t1 t2) (x : Job) (t : instant)
    (hs : scheduled_at sched x t = true) : pending sched x t = true :=
  H.vs.2 x t hs

private theorem scb_must (H : ScbHyps JLFP arr_seq sched j t1 t2) : jobs_must_arrive_to_execute sched := by
  intro x t hs
  have h := scb_pending H x t hs
  unfold pending at h
  simp only [Bool.and_eq_true] at h
  exact h.1

private theorem scb_not_completed (H : ScbHyps JLFP arr_seq sched j t1 t2) (x : Job) (t : instant)
    (hs : scheduled_at sched x t = true) : completed_by sched x t = false := by
  have h := scb_pending H x t hs
  unfold pending at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

private theorem scb_cdne (H : ScbHyps JLFP arr_seq sched j t1 t2) : completed_jobs_dont_execute sched :=
  @valid_schedule_implies_completed_jobs_dont_execute Job _ _ sched _ _ basic_ready_instance arr_seq H.vs

private theorem scb_scheduled_in_prefix (H : ScbHyps JLFP arr_seq sched j t1 t2) (t : instant)
    (h1 : t1 ≤ t) (h2 : t < t2) : ∃ x, scheduled_job sched t = some x := by
  letI : JobReady Job (processor_state Job) := basic_ready_instance
  obtain ⟨x, hx⟩ := job_scheduled_in_busy_interval_prefix JLFP H.refl arr_seq H.va sched
    (basic_readiness_is_work_bearing_readiness arr_seq sched H.refl) H.vs H.wc j H.arr H.pos t1 t2 H.bip t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, h2⟩)
  exact ⟨x, (scheduled_at_iff_scheduled_job sched x t).1 hx⟩

/-- Every schedule change strictly inside the prefix is a priority bump or a job completion. -/
private theorem scb_change_cause (H : ScbHyps JLFP arr_seq sched j t1 t2) (u : instant) (h1 : t1 < u)
    (h2 : u < t2) (hsc : schedule_change sched u = true) :
    (priority_bump sched u || (!priority_bump sched u && scb_comp arr_seq sched u)) = true := by
  cases hb : priority_bump sched u
  · simp only [Bool.false_or, Bool.not_false, Bool.true_and]
    obtain ⟨jo, hjo⟩ := scb_scheduled_in_prefix H u (by ((try dsimp only [instant, duration] at *); omega)) h2
    unfold schedule_change at hsc
    simp only [decide_eq_true_eq] at hsc
    have hpred : Nat.pred u = u - 1 := Nat.pred_eq_sub_one
    unfold priority_bump at hb
    rw [hjo] at hsc hb
    cases hs1 : scheduled_job sched (Nat.pred u) with
    | none => rw [hs1] at hb; simp at hb
    | some j1 =>
      rw [hs1] at hb hsc
      have hne : j1 ≠ jo := fun e => hsc (by rw [e])
      have hsched1 : scheduled_at sched j1 (u - 1) = true := by
        rw [← hpred]; exact (scheduled_at_iff_scheduled_job sched j1 _).2 hs1
      by_cases hc : completed_by sched j1 u = true
      · unfold scb_comp
        rw [List.any_eq_true]
        refine ⟨j1, ?_, ?_⟩
        · have := arrivals_up_to_scheduled_at arr_seq H.va.1 sched H.vs.1 (scb_must H) j1 (u - 1) hsched1 u
            (by ((try dsimp only [instant, duration] at *); omega))
          exact of_decide_eq_true this
        · unfold completes_at
          rw [scb_not_completed H j1 (u - 1) hsched1, hc]
          simp
      · exfalso
        have hnot : scheduled_at sched j1 u = false := by
          cases hx : scheduled_at sched j1 u
          · rfl
          · have := (scheduled_at_iff_scheduled_job sched j1 u).1 hx
            rw [hjo] at this
            exact absurd (Option.some.inj this).symm hne
        have hpre : preempted_at sched j1 u = true := by
          unfold preempted_at
          simp only [Bool.not_eq_true] at hc
          rw [hsched1, hc, hnot]; rfl
        have := H.nsp u j1 jo hpre ((scheduled_at_iff_scheduled_job sched jo u).2 hjo)
        simp only at hb
        exact absurd this (by simpa [JLFP_to_JLDP, hep_job_at] using hb)
  · simp

/-- A completion of a lower-priority job inside the prefix is a priority bump. -/
private theorem scb_lp_completion_bump (H : ScbHyps JLFP arr_seq sched j t1 t2) (u : instant) (h1 : t1 < u)
    (h2 : u < t2) (jlp : Job) (hlp : (!JLFP.hep_job jlp j) = true) (hc : completes_at sched jlp u = true) :
    priority_bump sched u = true := by
  letI : JobReady Job (processor_state Job) := basic_ready_instance
  have hs := scheduled_at_precedes_completes_at sched jlp u (by ((try dsimp only [instant, duration] at *); omega)) hc
  have hpt := completetion_time_is_preemption_time overheads_proc_model_is_a_uniprocessor_model arr_seq H.va
    sched H.vs.1 (scb_must H) (scb_cdne H) H.vpm jlp u hc
  obtain ⟨jh, _, hhep, hsh⟩ := not_quiet_implies_exists_scheduled_hp_job_after_preemption_point arr_seq H.va
    overheads_proc_model_is_a_uniprocessor_model sched JLFP H.refl H.trans H.vpm
    (basic_readiness_is_work_bearing_readiness arr_seq sched H.refl) H.vs H.wc H.resp j H.arr H.pos t1 t2 H.bip
    u u hpt
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by ((try dsimp only [instant, duration] at *); omega), h2⟩)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨le_refl _, h2⟩)
  have hpred : Nat.pred u = u - 1 := Nat.pred_eq_sub_one
  unfold priority_bump
  rw [(scheduled_at_iff_scheduled_job sched jh u).1 hsh, hpred,
    (scheduled_at_iff_scheduled_job sched jlp (u - 1)).1 hs]
  simp only [Bool.not_eq_true']
  cases hx : JLFP.hep_job jlp jh
  · rfl
  · have := H.trans jh jlp j hx hhep
    simp [this] at hlp

/-- The higher-or-equal-priority jobs arriving in `[t1, t)`. -/
private noncomputable def scb_hep (JLFP : JLFP_policy Job) (arr_seq : arrival_sequence Job) (j : Job)
    (t1 t : instant) : List Job :=
  (arrivals_between arr_seq t1 t).filter (fun x => JLFP.hep_job x j)

private theorem scb_bump_witness (H : ScbHyps JLFP arr_seq sched j t1 t2) (t : instant) (ht2 : t ≤ t2)
    (u : instant) (h1 : t1 < u) (h2 : u < t) (hb : priority_bump sched u = true) :
    ∃ x ∈ scb_hep JLFP arr_seq j t1 t, (priority_bump sched u && scheduled_at sched x u) = true := by
  letI : JobReady Job (processor_state Job) := basic_ready_instance
  obtain ⟨x, hs, hmem⟩ := priority_bump_implies_hp_arrival_in_prefix JLFP H.refl H.trans arr_seq H.va sched H.vs
    H.wc H.vpm H.resp j H.arr H.pos t1 t2 H.bip u t (by ((try dsimp only [instant, duration] at *); omega)) h2 ht2 hb
  refine ⟨x, ?_, by simp [hb, hs]⟩
  unfold scb_hep
  rw [List.mem_filter]
  refine ⟨of_decide_eq_true hmem, ?_⟩
  cases hx : JLFP.hep_job x j
  · exfalso
    have := lp_job_should_arrive_early_for_pi arr_seq H.va overheads_proc_model_is_a_uniprocessor_model sched
      JLFP H.trans H.vpm (basic_readiness_is_work_bearing_readiness arr_seq sched H.refl) H.vs H.resp j H.arr
      H.pos t1 t2 H.bip x (by simp [hx]) u t hmem ht2
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by ((try dsimp only [instant, duration] at *); omega), h2⟩)
    simp [hs] at this
  · rfl

private theorem scb_bump_unique (H : ScbHyps JLFP arr_seq sched j t1 t2) (t : instant) (ht2 : t ≤ t2)
    (x : Job) :
    (index_iota (t1 + 1) t).countP (fun u => priority_bump sched u && scheduled_at sched x u) ≤ 1 := by
  apply scb_countP_le_one _ _ (scb_nodup_index_iota _ _)
  -- two bump instants at which `x` is scheduled coincide
  have key : ∀ a b : instant, t1 + 1 ≤ a → a < b → b < t →
      (priority_bump sched a && scheduled_at sched x a) = true →
      (priority_bump sched b && scheduled_at sched x b) = true → False := by
    intro a b ha hab hb hpa hpb
    letI : JobReady Job (processor_state Job) := basic_ready_instance
    simp only [Bool.and_eq_true] at hpa hpb
    obtain ⟨jo, hjo⟩ := scb_scheduled_in_prefix H (b - 1) (by ((try dsimp only [instant, duration] at *); omega)) (by ((try dsimp only [instant, duration] at *); omega))
    have hsjo : scheduled_at sched jo (b - 1) = true := (scheduled_at_iff_scheduled_job sched jo _).2 hjo
    have hready : ∀ t' : Nat, (decide (a ≤ t') && decide (t' < b)) = true → job_ready sched x t' = true := by
      intro t' ht'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
      show pending sched x t' = true
      unfold pending
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · have := scb_must H x a hpa.2
        unfold has_arrived at this ⊢
        simp only [decide_eq_true_eq] at this ⊢
        ((try dsimp only [instant, duration] at *); omega)
      · cases hc : completed_by sched x t'
        · rfl
        · have := completion_monotonic sched x t' b (by ((try dsimp only [instant, duration] at *); omega)) hc
          rw [scb_not_completed H x b hpb.2] at this
          exact absurd this (by simp)
    have hhep := priority_higher_than_pending_job_priority overheads_proc_model_is_a_uniprocessor_model arr_seq
      H.va sched H.vpm JLFP H.refl H.vs H.resp x a b hpa.2 hpb.2 hready (b - 1)
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by ((try dsimp only [instant, duration] at *); omega), by ((try dsimp only [instant, duration] at *); omega)⟩) jo hsjo
    have hbump := hpb.1
    unfold priority_bump at hbump
    have hpred : Nat.pred b = b - 1 := Nat.pred_eq_sub_one
    rw [hpred, hjo, (scheduled_at_iff_scheduled_job sched x b).1 hpb.2] at hbump
    simp [hhep] at hbump
  intro a ha b hb hpa hpb
  have ha' := scb_mem_index_iota.1 ha
  have hb' := scb_mem_index_iota.1 hb
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact (key a b ha'.1 hab hb'.2 hpa hpb).elim
  · exact hab
  · exact (key b a hb'.1 hab ha'.2 hpb hpa).elim

private theorem scb_comp_witness (H : ScbHyps JLFP arr_seq sched j t1 t2) (t : instant) (ht2 : t ≤ t2)
    (u : instant) (h1 : t1 < u) (h2 : u < t)
    (hp : (!priority_bump sched u && scb_comp arr_seq sched u) = true) :
    ∃ x ∈ scb_hep JLFP arr_seq j t1 t, completes_at sched x u = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  unfold scb_comp at hp
  rw [List.any_eq_true] at hp
  obtain ⟨jc, hmem, hc⟩ := hp.2
  have harr : arrives_in arr_seq jc :=
    in_arrivals_implies_arrived arr_seq jc 0 (u + 1) (decide_eq_true hmem)
  have hs := scheduled_at_precedes_completes_at sched jc u (by ((try dsimp only [instant, duration] at *); omega)) hc
  have hhep : JLFP.hep_job jc j = true := by
    cases hx : JLFP.hep_job jc j
    · have := scb_lp_completion_bump H u h1 (by ((try dsimp only [instant, duration] at *); omega)) jc (by simp [hx]) hc
      rw [hp.1] at this; exact absurd this (by simp)
    · rfl
  refine ⟨jc, ?_, hc⟩
  unfold scb_hep
  rw [List.mem_filter]
  refine ⟨?_, hhep⟩
  apply of_decide_eq_true
  apply arrived_between_implies_in_arrivals arr_seq H.va.1 jc t1 t harr
  unfold arrived_between
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hle : job_arrival jc ≤ u - 1 := by
    have := scb_must H jc (u - 1) hs
    unfold has_arrived at this
    exact of_decide_eq_true this
  refine ⟨?_, by ((try dsimp only [instant, duration] at *); omega)⟩
  by_contra hlt
  have hbefore : decide (jc ∈ arrivals_before arr_seq t1) = true := by
    apply arrived_between_implies_in_arrivals arr_seq H.va.1 jc 0 t1 harr
    unfold arrived_between
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.zero_le _, by ((try dsimp only [instant, duration] at *); omega)⟩
  have := no_early_hep_job_completes_during_busy_prefix arr_seq H.va sched j u t1 t2 H.bip
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, by ((try dsimp only [instant, duration] at *); omega)⟩) jc hbefore hhep
  rw [hc] at this; exact absurd this (by simp)

omit [JobArrival Job] [JobPreemptable Job] in
private theorem scb_comp_unique (t : instant) (x : Job) :
    (index_iota (t1 + 1) t).countP (fun u => completes_at sched x u) ≤ 1 := by
  apply scb_countP_le_one _ _ (scb_nodup_index_iota _ _)
  have key : ∀ a b : instant, a < b → completes_at sched x a = true → completes_at sched x b = true → False := by
    intro a b hab ha hb
    unfold completes_at at ha hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at ha hb
    have := completion_monotonic sched x a (b - 1) (by ((try dsimp only [instant, duration] at *); omega)) ha.2
    rcases hb.1 with h | h
    · rw [this] at h; exact absurd h (by simp)
    · ((try dsimp only [instant, duration] at *); omega)
  intro a _ b _ hpa hpb
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab hpa hpb).elim
  · exact hab
  · exact (key b a hab hpb hpa).elim

/-- The number of schedule changes in `[t1 + 1, t)` is at most twice the number of higher-or-equal-priority
arrivals in `[t1, t)`. -/
private theorem scb_changes_le (H : ScbHyps JLFP arr_seq sched j t1 t2) (t : instant) (ht2 : t ≤ t2) :
    number_schedule_changes sched (t1 + 1) t ≤ 2 * (scb_hep JLFP arr_seq j t1 t).length := by
  unfold number_schedule_changes
  have h1 : (index_iota (t1 + 1) t).countP (schedule_change sched) ≤
      (index_iota (t1 + 1) t).countP
        (fun u => priority_bump sched u || (!priority_bump sched u && scb_comp arr_seq sched u)) := by
    apply List.countP_mono_left
    intro u hto hsc
    have := scb_mem_index_iota.1 hto
    exact scb_change_cause H u (by ((try dsimp only [instant, duration] at *); omega)) (by ((try dsimp only [instant, duration] at *); omega)) hsc
  have h2 := scb_countP_or_le (fun u => priority_bump sched u)
    (fun u => !priority_bump sched u && scb_comp arr_seq sched u) (index_iota (t1 + 1) t)
  have h3 := scb_count_le (index_iota (t1 + 1) t) (scb_hep JLFP arr_seq j t1 t) (fun u => priority_bump sched u)
    (fun u x => priority_bump sched u && scheduled_at sched x u)
    (fun u hto hb => by
      have := scb_mem_index_iota.1 hto
      exact scb_bump_witness H t ht2 u (by ((try dsimp only [instant, duration] at *); omega)) this.2 hb)
    (fun x _ => scb_bump_unique H t ht2 x)
  have h4 := scb_count_le (index_iota (t1 + 1) t) (scb_hep JLFP arr_seq j t1 t)
    (fun u => !priority_bump sched u && scb_comp arr_seq sched u)
    (fun u x => completes_at sched x u)
    (fun u hto hp => by
      have := scb_mem_index_iota.1 hto
      exact scb_comp_witness H t ht2 u (by ((try dsimp only [instant, duration] at *); omega)) this.2 hp)
    (fun x _ => scb_comp_unique (sched := sched) (t1 := t1) t x)
  ((try dsimp only [instant, duration] at *); omega)

/-- Under FIFO, no priority bumps occur, and the bound drops to the number of higher-or-equal-priority
arrivals. -/
private theorem scb_changes_le_fifo (H : ScbHyps JLFP arr_seq sched j t1 t2)
    (hfifo : ∀ j1 j2 : Job, JLFP.hep_job j1 j2 = decide (job_arrival j1 ≤ job_arrival j2)) (t : instant)
    (ht2 : t ≤ t2) :
    number_schedule_changes sched (t1 + 1) t ≤ (scb_hep JLFP arr_seq j t1 t).length := by
  unfold number_schedule_changes
  have h1 : (index_iota (t1 + 1) t).countP (schedule_change sched) ≤
      (index_iota (t1 + 1) t).countP (fun u => !priority_bump sched u && scb_comp arr_seq sched u) := by
    apply List.countP_mono_left
    intro u hto hsc
    have := scb_mem_index_iota.1 hto
    have hc := scb_change_cause H u (by ((try dsimp only [instant, duration] at *); omega)) (by ((try dsimp only [instant, duration] at *); omega)) hsc
    have hnb := no_priority_bumps_in_fifo JLFP H.refl H.trans arr_seq H.va sched H.vs H.wc H.vpm H.resp j H.arr
      H.pos t1 t2 H.bip hfifo u (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by ((try dsimp only [instant, duration] at *); omega), by ((try dsimp only [instant, duration] at *); omega)⟩)
    simp only [Bool.not_eq_true'] at hnb
    simpa [hnb] using hc
  have h4 := scb_count_le (index_iota (t1 + 1) t) (scb_hep JLFP arr_seq j t1 t)
    (fun u => !priority_bump sched u && scb_comp arr_seq sched u)
    (fun u x => completes_at sched x u)
    (fun u hto hp => by
      have := scb_mem_index_iota.1 hto
      exact scb_comp_witness H t ht2 u (by ((try dsimp only [instant, duration] at *); omega)) this.2 hp)
    (fun x _ => scb_comp_unique (sched := sched) (t1 := t1) t x)
  ((try dsimp only [instant, duration] at *); omega)

omit [JobArrival Job] [JobCost Job] [JobPreemptable Job] in
/-- Short intervals contain no schedule change of `[t1 + 1, t1 + Δ)`. -/
private theorem scb_short (sched : schedule (processor_state Job)) (t1 : instant) (Δ : duration)
    (h : Δ ≤ 1) : number_schedule_changes sched (t1 + 1) (t1 + Δ) = 0 := by
  unfold number_schedule_changes
  have : index_iota (t1 + 1) (t1 + Δ) = [] := by
    unfold index_iota
    have : t1 + Δ - (t1 + 1) = 0 := by ((try dsimp only [instant, duration] at *); omega)
    rw [this]; rfl
  rw [this]; rfl

end Setting

/-! ### Number of schedule changes is bounded -/

/-- Under JLFP scheduling, the number of schedule changes in `[t1 + 1, t1 + Δ)` is at most twice the number
of job arrivals across all tasks during `Δ`. -/
theorem schedule_changes_bounded_by_total_arrivals_JLFP {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] [JobPreemptable Job] (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP → transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := JLFP)) (processor_state Job) sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq
        sched JLFP →
      valid_preemption_model arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] [JobTask Job Task] (ts : List Task),
      all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ Δ : duration, t1 + Δ ≤ t2 →
      number_schedule_changes sched (t1 + 1) (t1 + Δ) ≤ 2 * sumSeq ts (fun tsk => max_arrivals tsk Δ) := by
  intro hrefl htrans arr_seq hva sched hvs hwc hnsp hresp hvpm j ha hpos t1 t2 hbip Task _ _ _ ts hall hrespma
    Δ hsub
  by_cases hΔ : Δ ≤ 1
  · rw [scb_short sched t1 Δ hΔ]; exact Nat.zero_le _
  · have H : ScbHyps JLFP arr_seq sched j t1 t2 :=
      ⟨hrefl, htrans, hva, hvs, hwc, hnsp, hresp, hvpm, ha, hpos, hbip⟩
    have h1 := scb_changes_le H (t1 + Δ) hsub
    have h2 := jlfp_hep_arrivals_bounded_by_sum_max_arrivals arr_seq ts hall hrespma j t1 Δ
    unfold scb_hep at h1
    ((try dsimp only [instant, duration] at *); omega)

/-- Under FP scheduling, the number of schedule changes in `[t1 + 1, t1 + Δ)` is at most twice the number of
arrivals of tasks with higher-or-equal priority than the task of `j` during `Δ`. -/
theorem schedule_changes_bounded_by_total_arrivals_FP {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    (FP : FP_policy Task) {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task] [JobCost Job]
    [JobPreemptable Job] :
    reflexive_task_priorities FP → transitive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := FP_to_JLFP FP)) (processor_state Job) sched →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ (processor_state Job) _ basic_ready_instance
        arr_seq sched FP →
      valid_preemption_model arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, @busy_interval_prefix Job _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) j t1 t2 →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ Δ : duration, t1 + Δ ≤ t2 →
      number_schedule_changes sched (t1 + 1) (t1 + Δ) ≤
        2 * sumFiltered ts (fun tsk => hep_task tsk (job_task (Task := Task) j)) (fun tsk => max_arrivals tsk Δ) := by
  intro hrefl htrans arr_seq hva sched hvs hwc hnsp hresp hvpm j ha hpos t1 t2 hbip ts hall hrespma Δ hsub
  by_cases hΔ : Δ ≤ 1
  · rw [scb_short sched t1 Δ hΔ]; exact Nat.zero_le _
  · have H : ScbHyps (FP_to_JLFP FP) arr_seq sched j t1 t2 :=
      ⟨reflexive_priorities_FP_implies_JLFP FP hrefl, transitive_priorities_FP_implies_JLFP FP htrans, hva, hvs,
        hwc, hnsp, hresp, hvpm, ha, hpos, hbip⟩
    have h1 := scb_changes_le H (t1 + Δ) hsub
    have h2 := fp_hep_arrivals_bounded_by_sum_max_arrivals (FP := FP) arr_seq ts hall hrespma j t1 Δ
    unfold scb_hep at h1
    ((try dsimp only [instant, duration] at *); omega)

/-- Under FIFO scheduling, the number of schedule changes in `[t1 + 1, t1 + Δ)` is at most the number of job
arrivals across all tasks during `Δ`. -/
theorem schedule_changes_bounded_by_total_arrivals_FIFO {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] [JobPreemptable Job] (JLFP : JLFP_policy Job) :
    policy_is_FIFO JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := JLFP)) (processor_state Job) sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq
        sched JLFP →
      valid_preemption_model arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] [JobTask Job Task] (ts : List Task),
      all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ Δ : duration, t1 + Δ ≤ t2 →
      number_schedule_changes sched (t1 + 1) (t1 + Δ) ≤ sumSeq ts (fun tsk => max_arrivals tsk Δ) := by
  intro hfifo arr_seq hva sched hvs hwc hnsp hresp hvpm j ha hpos t1 t2 hbip Task _ _ _ ts hall hrespma Δ hsub
  by_cases hΔ : Δ ≤ 1
  · rw [scb_short sched t1 Δ hΔ]; exact Nat.zero_le _
  · have hf : ∀ j1 j2 : Job, JLFP.hep_job j1 j2 = decide (job_arrival j1 ≤ job_arrival j2) := hfifo
    have hrefl : reflexive_job_priorities JLFP := fun x => by rw [hf]; simp
    have htrans : transitive_job_priorities JLFP := by
      intro y x z hxy hyz
      rw [hf] at hxy hyz ⊢
      simp only [decide_eq_true_eq] at hxy hyz ⊢
      ((try dsimp only [instant, duration] at *); omega)
    have H : ScbHyps JLFP arr_seq sched j t1 t2 :=
      ⟨hrefl, htrans, hva, hvs, hwc, hnsp, hresp, hvpm, ha, hpos, hbip⟩
    have h1 := scb_changes_le_fifo H hf (t1 + Δ) hsub
    have h2 := jlfp_hep_arrivals_bounded_by_sum_max_arrivals arr_seq ts hall hrespma j t1 Δ
    unfold scb_hep at h1
    ((try dsimp only [instant, duration] at *); omega)

end Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound
