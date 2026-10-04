-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/ideal/iw_instantiation.v

import Prosa.Analysis.Facts.BusyInterval.CarryIn
import Prosa.Analysis.Abstract.IBF.Task
import Prosa.Analysis.Facts.Interference
import Prosa.Model.Processor.Ideal
import Prosa.Analysis.Facts.Model.Ideal.PriorityInversion

namespace Prosa.Analysis.Abstract.Ideal.IwInstantiation

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Ideal
open Prosa.Model.Processor.Supply
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Definitions.BusyInterval
open Prosa.Analysis.Definitions.TaskSchedule
open Prosa.Model.Task.Sequentiality
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Model.Ideal.PriorityInversion
open Prosa.Analysis.Facts.Model.TaskSchedule
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.BusyInterval.CarryIn
open Prosa.Analysis.Facts.BusyInterval.Existence
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Util.Sum
open Prosa.Util.Notation

/-! JLFP instantiation of interference and interfering workload for ideal
uniprocessor schedules, and their equivalence with the classical notions.

Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
The source's section-local instances `ideal_jlfp_interference` and
`ideal_jlfp_interfering_workload` are the definitions of the same names below
(the source `Instance` fields, with the Boolean priority inversion counted by
`Bool.toNat` as the source's `nat_of_bool` coercion), passed explicitly
wherever the elaborated statements use them implicitly. The classical and
abstract busy-interval notions are distinguished by namespace, as the source
distinguishes them by module qualification. Representation: a Boolean in
`Prop` position is `= true`; `~~ b` is `!b`; `a <= b < c` is a Boolean
conjunction of decides; `tsk \in ts` is `decide (tsk ∈ ts) = true`. -/

/-- A half-open `sumSeq` over `List.range'` is the corresponding `Finset.Ico` sum. -/
private theorem sumSeq_range'_eq (a b : Nat) (f : Nat → Nat) :
    sumSeq (List.range' a (b - a)) f = ∑ t ∈ (Finset.Ico a b : Finset Nat), f t := by
  unfold sumSeq
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∀ n a, ((List.range' a n).map f).sum = ∑ k ∈ Finset.range n, f (a + k) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1), Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_assoc, Nat.add_comm 1 k]
  exact this (b - a) a


section JLFPInstantiation

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- A job incurs interference if it incurs a priority inversion or another
higher-or-equal-priority job is served. -/
@[reducible] noncomputable def ideal_jlfp_interference (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) [JLFP_policy Job] : Interference Job where
  interference j t := priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t

/-- The interfering workload is the priority inversion plus the workload of
other higher-or-equal-priority jobs released at `t`. -/
@[reducible] noncomputable def ideal_jlfp_interfering_workload [JobCost Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) [JLFP_policy Job] : InterferingWorkload Job where
  interfering_workload j t :=
    (priority_inversion arr_seq sched j t).toNat + other_hep_jobs_interfering_workload arr_seq j t

theorem no_interference_when_idle [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job] (t : instant), ideal_is_idle sched t = true →
      ∀ j : Job, (!@Interference.interference Job _ (ideal_jlfp_interference arr_seq sched) j t) = true := by
  intro hva sched hfrom hmust JLFP t hidle j
  have h1 := idle_implies_no_priority_inversion arr_seq hva sched hfrom hmust j t hidle
  have hidle' : is_idle arr_seq sched t = true := by
    rw [is_idle_def Job arr_seq sched hfrom hmust hva t]; exact hidle
  have h2 := no_hep_job_interference_when_idle arr_seq hva sched hfrom hmust JLFP t hidle' j
  have e1 : priority_inversion arr_seq sched j t = false := by simpa using h1
  have e2 : another_hep_job_interference arr_seq sched j t = false := by simpa using h2
  show (!(priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t)) = true
  rw [e1, e2]; rfl

theorem no_task_interference_when_idle [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job] (t : instant), ideal_is_idle sched t = true →
      ∀ j : Job, (!@task_interference Job _ Task _ _ _ arr_seq sched (ideal_jlfp_interference arr_seq sched) j t) = true := by
  intro hva sched hfrom hmust JLFP t hidle j
  have h := no_interference_when_idle arr_seq hva sched hfrom hmust t hidle j
  unfold task_interference cond_interference
  simp only [Bool.not_eq_true'] at h ⊢
  rw [h, Bool.and_false]

theorem task_interference_eq_false [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job] (tsk : Task) (j : Job), job_of_task tsk j = true →
      ∀ (t : instant) (j' : Job), job_of_task tsk j' = true → scheduled_at sched j' t = true →
        (!@task_interference Job _ Task _ _ _ arr_seq sched (ideal_jlfp_interference arr_seq sched) j t) = true := by
  intro hva sched hfrom hmust _ tsk j hj t j' hj' hs
  have hts := task_served_eq_task_scheduled arr_seq hva (processor_state Job) sched hfrom hmust
    (job_task (Task := Task) j) (ideal_proc_model_ensures_ideal_progress Job) t
  have hjs := job_of_scheduled_task arr_seq hva (processor_state Job) (ideal_proc_model_is_a_uniprocessor_model Job)
    sched hfrom hmust (job_task (Task := Task) j) j' t hs
  have hjt : job_of_task (job_task (Task := Task) j) j' = true := by
    unfold job_of_task at hj hj' ⊢
    rw [of_decide_eq_true hj', of_decide_eq_true hj]; simp
  unfold task_interference cond_interference nonself
  rw [hts, hjs, hjt]; rfl

theorem sched_athep_implies_task_interference [JobTask Job Task] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job] (tsk : Task) (j : Job), job_of_task tsk j = true →
      ∀ (t : instant) (j' : Job), (!job_of_task tsk j') = true → scheduled_at sched j' t = true →
        hep_job j' j = true →
        @task_interference Job _ Task _ _ _ arr_seq sched (ideal_jlfp_interference arr_seq sched) j t = true := by
  intro hva sched hfrom hmust _ tsk j hj t j' hj' hs hhep
  have hts := task_served_eq_task_scheduled arr_seq hva (processor_state Job) sched hfrom hmust
    (job_task (Task := Task) j) (ideal_proc_model_ensures_ideal_progress Job) t
  have hjs := job_of_scheduled_task arr_seq hva (processor_state Job) (ideal_proc_model_is_a_uniprocessor_model Job)
    sched hfrom hmust (job_task (Task := Task) j) j' t hs
  have hjt : job_of_task (job_task (Task := Task) j) j' = false := by
    unfold job_of_task at hj hj' ⊢
    rw [of_decide_eq_true hj]; simpa using hj'
  have hne : j' ≠ j := by
    intro h; subst h
    unfold job_of_task at hj hj'; rw [hj] at hj'; exact Bool.false_ne_true (by simpa using hj')
  have hserved := scheduled_at_implies_in_served_at arr_seq hva sched hfrom hmust
    (ideal_proc_model_ensures_ideal_progress Job) j' t hs
  unfold task_interference cond_interference nonself
  rw [hts, hjs, hjt]
  show (true && (priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t)) = true
  simp only [Bool.true_and, Bool.or_eq_true]
  right
  unfold another_hep_job_interference
  rw [List.any_eq_true]
  refine ⟨j', of_decide_eq_true hserved, ?_⟩
  unfold another_hep_job
  simp [hhep, hne]

theorem cumulative_interference_split [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ (j : Job) (t1 t2 : Nat),
      @cumulative_interference Job _ (ideal_jlfp_interference arr_seq sched) j t1 t2 =
        cumulative_priority_inversion arr_seq sched j t1 t2 +
          cumulative_another_hep_job_interference arr_seq sched j t1 t2 := by
  intro hva sched hfrom hmust JLFP hrefl j t1 t2
  unfold cumulative_interference cumul_cond_interference cumulative_priority_inversion
    cumulative_another_hep_job_interference
  rw [sumSeq_range'_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  show (true && (priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t)).toNat =
    (priority_inversion arr_seq sched j t).toNat + (another_hep_job_interference arr_seq sched j t).toNat
  rcases ideal_proc_model_sched_case_analysis Job sched t with hidle | ⟨s, hs⟩
  · have e : priority_inversion arr_seq sched j t = false := by
      simpa using idle_implies_no_priority_inversion arr_seq hva sched hfrom hmust j t hidle
    rw [e]; cases another_hep_job_interference arr_seq sched j t <;> rfl
  · cases hhep : hep_job s j
    · have e1 := sched_lp_implies_priority_inversion arr_seq hva sched hfrom hmust hrefl j t s hs (by simp [hhep])
      have e2 : another_hep_job_interference arr_seq sched j t = false := by
        simpa using no_ahep_interference_when_scheduled_lp (ideal_proc_model_is_a_uniprocessor_model Job)
          arr_seq sched JLFP j t s hs (by simp [hhep])
      rw [e1, e2]; rfl
    · have e1 := sched_hep_implies_no_priority_inversion arr_seq hva sched hfrom hmust hrefl j t s hs hhep
      rw [e1]; cases another_hep_job_interference arr_seq sched j t <;> rfl

theorem cumulative_interfering_workload_split [JobCost Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) [JLFP_policy Job] (j : Job) (t1 t2 : Nat) :
    @cumulative_interfering_workload Job _ (ideal_jlfp_interfering_workload arr_seq sched) j t1 t2 =
      cumulative_priority_inversion arr_seq sched j t1 t2 +
        cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2 := by
  unfold cumulative_interfering_workload cumulative_priority_inversion cumulative_other_hep_jobs_interfering_workload
  rw [sumSeq_range'_eq, ← Finset.sum_add_distrib]
  rfl

private theorem sumFiltered_append' {I : Type _} (l1 l2 : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  unfold sumFiltered
  rw [List.filter_append, List.map_append, List.sum_append]

theorem cumulative_iw_hep_eq_workload_of_ohep [JobCost Job] (arr_seq : arrival_sequence Job) [JLFP_policy Job]
    (t1 t2 : instant) (j : Job) :
    cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2 = workload_of_other_hep_jobs arr_seq j t1 t2 := by
  unfold cumulative_other_hep_jobs_interfering_workload workload_of_other_hep_jobs workload_of_jobs
  rcases Nat.lt_or_ge t1 t2 with hlt | hge
  · obtain ⟨k, rfl⟩ : ∃ k, t2 = t1 + k := ⟨t2 - t1, by omega'⟩
    rw [Nat.add_sub_cancel_left]
    clear hlt
    induction k with
    | zero =>
      rw [arrivals_between_geq arr_seq t1 (t1 + 0) (by omega')]
      rfl
    | succ k ih =>
      rw [List.range'_concat, sumSeq, List.map_append, List.sum_append, ← sumSeq, ih,
        arrivals_between_cat arr_seq t1 (t1 + k) (t1 + (k + 1)) (by omega') (by omega'), sumFiltered_append']
      congr 1
      have : arrivals_between arr_seq (t1 + k) (t1 + (k + 1)) = arrivals_at arr_seq (t1 + k) := by
        unfold arrivals_between bigCat
        rw [show t1 + (k + 1) - (t1 + k) = 1 by omega']
        simp
      rw [this]
      simp [other_hep_jobs_interfering_workload]
  · rw [show t2 - t1 = 0 by omega', arrivals_between_geq arr_seq t1 t2 hge]
    rfl

theorem cumulative_task_interference_split [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ (tsk : Task) (j : Job) (t1 : Nat) (t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
      (!completed_by sched j t2) = true →
      @cumul_task_interference Job _ Task _ _ _ arr_seq sched (ideal_jlfp_interference arr_seq sched) j t1 t2 ≤
        cumulative_priority_inversion arr_seq sched j t1 t2 +
          cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j t1 t2 := by
  intro hva sched hfrom hmust JLFP hrefl tsk j t1 t2 _ _ _
  unfold cumul_task_interference cumul_cond_interference cumulative_priority_inversion
    cumulative_another_task_hep_job_interference
  rw [sumSeq_range'_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  unfold cond_interference nonself
  show ((!task_served_at arr_seq sched (job_task (Task := Task) j) t) &&
      (priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t)).toNat ≤
    (priority_inversion arr_seq sched j t).toNat +
      (another_task_hep_job_interference (Task := Task) arr_seq sched j t).toNat
  rcases ideal_proc_model_sched_case_analysis Job sched t with hidle | ⟨s, hs⟩
  · have e1 : priority_inversion arr_seq sched j t = false := by
      simpa using idle_implies_no_priority_inversion arr_seq hva sched hfrom hmust j t hidle
    have hidle' : is_idle arr_seq sched t = true := by
      rw [is_idle_def Job arr_seq sched hfrom hmust hva t]; exact hidle
    have e2 : another_hep_job_interference arr_seq sched j t = false := by
      simpa using no_hep_job_interference_when_idle arr_seq hva sched hfrom hmust JLFP t hidle' j
    rw [e1, e2]; simp
  · have hts := task_served_eq_task_scheduled arr_seq hva (processor_state Job) sched hfrom hmust
      (job_task (Task := Task) j) (ideal_proc_model_ensures_ideal_progress Job) t
    have hjs := job_of_scheduled_task arr_seq hva (processor_state Job) (ideal_proc_model_is_a_uniprocessor_model Job)
      sched hfrom hmust (job_task (Task := Task) j) s t hs
    have hahep := interference_ahep_def (ideal_proc_model_is_a_uniprocessor_model Job)
      (ideal_proc_model_fully_consuming Job) arr_seq hva sched hfrom hmust JLFP j t
      (ideal_proc_has_supply Job sched t) s hs
    have hathep := interference_athep_def (Task := Task) (ideal_proc_model_is_a_uniprocessor_model Job)
      (ideal_proc_model_fully_consuming Job) arr_seq hva sched hfrom hmust JLFP j t
      (ideal_proc_has_supply Job sched t) s hs
    have hpi := priority_inversion_equiv_sched_lower_priority arr_seq hva sched hfrom hmust hrefl j t s hs
    rw [hts, hjs, hahep, hathep, hpi]
    unfold job_of_task another_hep_job another_task_hep_job
    by_cases hst : job_task (Task := Task) s = job_task (Task := Task) j
    · simp [hst]
    · have hsj : s ≠ j := fun h => hst (h ▸ rfl)
      cases hep_job s j <;> simp [hst, hsj]

private theorem classical_quiet_time_zero [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) [JLFP_policy Job] (j : Job) :
    Classical.quiet_time arr_seq sched j 0 := by
  intro jhp _ _ hab
  unfold arrived_before at hab
  simp at hab

/-- The other higher-or-equal-priority part of the abstract quiet-time
equation is the workload/service equation of the other hep jobs. -/
private theorem ohep_equation [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (sched : schedule (processor_state Job))
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq) (hmust : jobs_must_arrive_to_execute sched)
    (hcde : completed_jobs_dont_execute sched) [JLFP : JLFP_policy Job] (hrefl : reflexive_job_priorities JLFP)
    (j : Job) (t : instant) :
    (@cumulative_interference Job _ (ideal_jlfp_interference arr_seq sched) j 0 t = @cumulative_interfering_workload Job _ (ideal_jlfp_interfering_workload arr_seq sched) j 0 t) ↔
      service_of_other_hep_jobs arr_seq sched j 0 t = workload_of_other_hep_jobs arr_seq j 0 t := by
  rw [cumulative_interference_split arr_seq hva sched hfrom hmust hrefl j 0 t,
    cumulative_interfering_workload_split arr_seq sched j 0 t,
    cumulative_i_ohep_eq_service_of_ohep (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva sched hmust hcde
      JLFP (ideal_proc_model_provides_unit_service Job) j 0 t (classical_quiet_time_zero arr_seq sched j),
    cumulative_iw_hep_eq_workload_of_ohep]
  omega'

theorem quiet_time_cl_implies_quiet_time_ab [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t : instant, Classical.quiet_time arr_seq sched j t →
      @Prosa.Analysis.Abstract.Definitions.quiet_time Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t = true := by
  intro hva sched hfrom hmust hcde JLFP hrefl j _ t hqt
  unfold Prosa.Analysis.Abstract.Definitions.quiet_time
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rw [ohep_equation arr_seq hva sched hfrom hmust hcde hrefl j t]
    unfold service_of_other_hep_jobs workload_of_other_hep_jobs
    symm
    apply (all_jobs_have_completed_equiv_workload_eq_service (ideal_proc_model_provides_unit_service Job) arr_seq
      hva.1 sched hmust hcde _ 0 t t).mp
    intro j0 hin hP
    have hbt := in_arrivals_implies_arrived_between arr_seq hva.1 j0 0 t hin
    unfold another_hep_job at hP
    simp only [Bool.and_eq_true] at hP
    apply hqt j0 (in_arrivals_implies_arrived arr_seq j0 0 t hin) hP.1
    unfold arrived_between at hbt; unfold arrived_before
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
    exact decide_eq_true hbt.2
  · unfold pending_earlier_and_at
    cases hab : arrived_before j t
    · rfl
    · have := hqt j (by assumption) (hrefl j) hab
      simp [this]

theorem quiet_time_ab_implies_quiet_time_cl [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t : instant, @Prosa.Analysis.Abstract.Definitions.quiet_time Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t = true →
      Classical.quiet_time arr_seq sched j t := by
  intro hva sched hfrom hmust hcde JLFP hrefl j hj _ t hqa
  unfold Prosa.Analysis.Abstract.Definitions.quiet_time at hqa
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hqa
  obtain ⟨h0, h1⟩ := hqa
  rw [ohep_equation arr_seq hva sched hfrom hmust hcde hrefl j t] at h0
  unfold service_of_other_hep_jobs workload_of_other_hep_jobs at h0
  have hjc : arrived_before j t = true → completed_by sched j t = true := by
    intro hab
    unfold pending_earlier_and_at at h1
    rw [hab] at h1
    simpa using h1
  have hB : workload_of_jobs (fun x => hep_job x j && !decide (x ≠ j)) (arrivals_between arr_seq 0 t) =
      service_of_jobs sched (fun x => hep_job x j && !decide (x ≠ j)) (arrivals_between arr_seq 0 t) 0 t := by
    apply (all_jobs_have_completed_equiv_workload_eq_service (ideal_proc_model_provides_unit_service Job) arr_seq
      hva.1 sched hmust hcde _ 0 t t).mp
    intro x hin hP
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hP
    rw [hP.2]
    apply hjc
    have hbt := in_arrivals_implies_arrived_between arr_seq hva.1 x 0 t hin
    rw [hP.2] at hbt
    unfold arrived_between at hbt; unfold arrived_before
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
    exact decide_eq_true hbt.2
  have hall : workload_of_jobs (fun x => hep_job x j) (arrivals_between arr_seq 0 t) =
      service_of_jobs sched (fun x => hep_job x j) (arrivals_between arr_seq 0 t) 0 t := by
    rw [workload_of_jobs_case_on_pred _ _ (fun x => decide (x ≠ j)),
      service_of_jobs_case_on_pred sched _ 0 t _ (fun x => decide (x ≠ j)), hB]
    congr 1
    exact h0.symm
  intro jhp hjhp hhep hab
  apply (all_jobs_have_completed_equiv_workload_eq_service (ideal_proc_model_provides_unit_service Job) arr_seq
    hva.1 sched hmust hcde _ 0 t t).mpr hall jhp _ hhep
  unfold arrived_before at hab
  exact job_in_arrivals_between arr_seq hva.1 jhp 0 t hjhp (Nat.zero_le _) (of_decide_eq_true hab)

theorem instantiated_quiet_time_equivalent_quiet_time [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t : instant, Classical.quiet_time arr_seq sched j t ↔ @Prosa.Analysis.Abstract.Definitions.quiet_time Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t = true := by
  intro hva sched hfrom hmust hcde JLFP hrefl j hj hpos t
  exact ⟨quiet_time_cl_implies_quiet_time_ab arr_seq hva sched hfrom hmust hcde hrefl j hj t,
    quiet_time_ab_implies_quiet_time_cl arr_seq hva sched hfrom hmust hcde hrefl j hj hpos t⟩

theorem instantiated_busy_interval_prefix_equivalent_busy_interval_prefix [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, Classical.busy_interval_prefix arr_seq sched j t1 t2 ↔ @Prosa.Analysis.Abstract.Definitions.busy_interval_prefix Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 := by
  intro hva sched hfrom hmust hcde JLFP hrefl j hj hpos t1 t2
  have hq := instantiated_quiet_time_equivalent_quiet_time arr_seq hva sched hfrom hmust hcde hrefl j hj hpos
  unfold Classical.busy_interval_prefix Prosa.Analysis.Abstract.Definitions.busy_interval_prefix
  constructor
  · rintro ⟨_, hqt1, hnq, harr⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
    refine ⟨harr, (hq t1).mp hqt1, ?_⟩
    intro t ht hqa
    exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ht) ((hq t).mpr hqa)
  · rintro ⟨harr, hqa1, hnq⟩
    refine ⟨by omega', (hq t1).mpr hqa1, ?_, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact harr⟩
    intro t ht hqt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact hnq t ht ((hq t).mp hqt)

theorem instantiated_busy_interval_equivalent_busy_interval [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, Classical.busy_interval arr_seq sched j t1 t2 ↔ @Prosa.Analysis.Abstract.Definitions.busy_interval Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 := by
  intro hva sched hfrom hmust hcde JLFP hrefl j hj hpos t1 t2
  have hp := instantiated_busy_interval_prefix_equivalent_busy_interval_prefix arr_seq hva sched hfrom hmust hcde
    hrefl j hj hpos t1 t2
  have hq := instantiated_quiet_time_equivalent_quiet_time arr_seq hva sched hfrom hmust hcde hrefl j hj hpos t2
  unfold Classical.busy_interval Prosa.Analysis.Abstract.Definitions.busy_interval
  exact ⟨fun h => ⟨hp.mp h.1, hq.mp h.2⟩, fun h => ⟨hp.mpr h.1, hq.mpr h.2⟩⟩

theorem abstract_busy_interval_classic_quiet_time [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 → Classical.quiet_time arr_seq sched j t1 := by
  intro hva sched hfrom hmust hcde JLFP hrefl j hj hpos t1 t2 hb
  exact ((instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hrefl j hj hpos
    t1 t2).mpr hb).1.2.1

theorem abstract_busy_interval_classic_busy_interval_prefix [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 → Classical.busy_interval_prefix arr_seq sched j t1 t2 := by
  intro hva sched hfrom hmust hcde JLFP hrefl j hj hpos t1 t2 hb
  exact ((instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hrefl j hj hpos
    t1 t2).mpr hb).1

theorem not_interference_implies_scheduled [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ [JobReady0 : JobReady Job (processor_state Job)], work_bearing_readiness arr_seq sched →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched → reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → 0 < job_cost j →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval_prefix Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ¬ @Interference.interference Job _ (ideal_jlfp_interference arr_seq sched) j t = true → receives_service_at sched j t = true := by
  intro hva sched hfrom hmust hcde JLFP hrefl _ hwbr hwc _ j hj hpos t1 t2 hbp t ht hnint
  have hni : (priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t) = false := by
    have := Bool.eq_false_iff.mpr hnint
    exact this
  simp only [Bool.or_eq_false_iff] at hni
  obtain ⟨hpi, hahi⟩ := hni
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  rcases ideal_proc_model_sched_case_analysis Job sched t with hidle | ⟨jo, hs⟩
  · exfalso
    have hcl := (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix arr_seq hva sched hfrom hmust hcde
      hrefl j hj hcp t1 t2).mpr hbp
    apply not_quiet_implies_not_idle arr_seq hva sched hfrom hmust JLFP hwbr j hj hcp hwc hrefl t1 t2 hcl t ht
    rw [is_idle_def Job arr_seq sched hfrom hmust hva t]; exact hidle
  · have hahep := interference_ahep_def (ideal_proc_model_is_a_uniprocessor_model Job)
      (ideal_proc_model_fully_consuming Job) arr_seq hva sched hfrom hmust JLFP j t
      (ideal_proc_has_supply Job sched t) jo hs
    rw [hahep] at hahi
    by_cases hjo : jo = j
    · subst hjo
      unfold receives_service_at
      rw [service_at_is_scheduled_at, hs]; rfl
    · exfalso
      cases hhep : hep_job jo j
      · have := sched_lp_implies_priority_inversion arr_seq hva sched hfrom hmust hrefl j t jo hs (by simp [hhep])
        rw [hpi] at this; exact Bool.false_ne_true this
      · unfold another_hep_job at hahi
        simp [hhep, hjo] at hahi

theorem scheduled_implies_no_interference [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP → reflexive_job_priorities JLFP →
    ∀ (j : Job) (t : instant), receives_service_at sched j t = true → ¬ @Interference.interference Job _ (ideal_jlfp_interference arr_seq sched) j t = true := by
  intro hva sched hfrom hmust JLFP hrefl _ j t hrs
  have hs : scheduled_at sched j t = true := by
    unfold receives_service_at at hrs
    rw [service_at_is_scheduled_at] at hrs
    cases h : scheduled_at sched j t
    · rw [h] at hrs; simp at hrs
    · rfl
  have e1 := sched_hep_implies_no_priority_inversion arr_seq hva sched hfrom hmust hrefl j t j hs (hrefl j)
  have e2 : another_hep_job_interference arr_seq sched j t = false := by
    simpa using no_ahep_interference_when_scheduled (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq sched
      JLFP j t hs
  show ¬ (priority_inversion arr_seq sched j t || another_hep_job_interference arr_seq sched j t) = true
  rw [e1, e2]; simp

theorem instantiated_i_and_w_are_coherent_with_schedule [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ [JobReady0 : JobReady Job (processor_state Job)], work_bearing_readiness arr_seq sched →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched → reflexive_job_priorities JLFP →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ arr_seq sched := by
  intro hva sched hfrom hmust hcde JLFP hrefl _ hwbr hwc hrefl' j t1 t2 t hj hpos hbp ht
  constructor
  · exact not_interference_implies_scheduled arr_seq hva sched hfrom hmust hcde hrefl hwbr hwc hrefl' j hj hpos
      t1 t2 hbp t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ht)
  · exact scheduled_implies_no_interference arr_seq hva sched hfrom hmust hrefl hrefl' j t

theorem instantiated_interference_and_workload_consistent_with_sequential_tasks [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ tsk : Task, policy_respects_sequential_tasks (Task := Task) JLFP →
      @interference_and_workload_consistent_with_sequential_tasks Job _ Task _ _ _ _ _ arr_seq sched tsk (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) := by
  intro hva sched hfrom hmust hcde JLFP hrefl tsk hseq j t1 t2 hj htsk hpos hb
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hrefl j hj hcp
    t1 t2).mpr hb
  obtain ⟨⟨_, hqt, _, harr⟩, _⟩ := hcl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  unfold task_workload_between task_workload task_service_of_jobs_in
  apply (all_jobs_have_completed_equiv_workload_eq_service (ideal_proc_model_provides_unit_service Job) arr_seq
    hva.1 sched hmust hcde _ 0 t1 t1).mp
  intro s hin hst
  have hbt := in_arrivals_implies_arrived_between arr_seq hva.1 s 0 t1 hin
  unfold arrived_between at hbt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
  apply hqt s (in_arrivals_implies_arrived arr_seq s 0 t1 hin)
  · apply hseq s j
    · unfold job_of_task at hst htsk
      rw [of_decide_eq_true hst, of_decide_eq_true htsk]; simp
    · omega'
  · unfold arrived_before; exact decide_eq_true hbt.2

theorem instantiated_busy_intervals_are_bounded [TaskCost Task] [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job), jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ (tsk : Task) [JobReady0 : JobReady Job (processor_state Job)], work_bearing_readiness arr_seq sched →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
    ∀ [MaxArrivals Task] (ts : List Task), taskset_respects_max_arrivals arr_seq ts →
      all_jobs_from_taskset arr_seq ts →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
      @busy_intervals_are_bounded_by Job _ (ideal_jlfp_interference arr_seq sched) (ideal_jlfp_interfering_workload arr_seq sched) _ _ _ arr_seq sched Task _ _ tsk L := by
  intro hva sched hfrom hmust hcde JLFP hrefl tsk _ hwbr hwc _ ts hresp hfromts L hL hfix hvjc j hj htsk hpos
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  obtain ⟨t1, t2, h1, h2, hb⟩ := busy_interval_from_total_workload_bound arr_seq hva
    (ideal_proc_model_is_a_uniprocessor_model Job) (ideal_proc_model_fully_consuming Job) sched hfrom hmust hcde
    JLFP hrefl hwbr hwc L hL
    (by
      intro t _
      have hbl : blackout_during sched t (t + L) = 0 := by
        unfold blackout_during
        apply Finset.sum_eq_zero
        intro x _
        unfold is_blackout
        rw [ideal_proc_has_supply Job sched x]; rfl
      rw [hbl, Nat.zero_add]
      have := total_workload_le_total_rbf arr_seq hvjc ts hfromts hresp t L
      omega')
    (ideal_proc_model_provides_unit_service Job) j hj hcp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨t1, t2, h1, h2, (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde
    hrefl j hj hcp t1 t2).mp hb⟩

end JLFPInstantiation

end Prosa.Analysis.Abstract.Ideal.IwInstantiation
