-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/bounded_bi/edf.v

import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Definitions.BusyInterval.EdfPiBound
import Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary
import Prosa.Analysis.Definitions.Sbf.Busy

namespace Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Edf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Edf
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BusyInterval.EdfPiBound
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Rbf

/-! Bounded busy intervals under EDF scheduling on a restricted-supply
uniprocessor: `total_rbf L ≤ SBF L` together with
`longest_busy_interval_with_pi ts tsk ≤ SBF L` bounds the busy intervals of
`tsk` by `L`.

Binders follow the elaborated source types: each declaration takes the
section inputs and hypotheses it uses, in their elaborated order (the unused
arrival-curve validity hypothesis is absent, as in the elaborated types);
instance inputs quantified after a hypothesis are `∀ [..]` binders at that
position. The EDF policy is the accepted `EDF` instance over the accepted
`job_deadline_from_task_deadline` instance, named explicitly. The source's
section-local instances `rs_jlfp_interference` and
`rs_jlfp_interfering_workload` are the accepted definitions of the same names
over that policy, passed explicitly where the elaborated statements use them
implicitly. The busy-SBF validity is the classical one of
`analysis/definitions/sbf/busy.v`; the supply bound function is applied
through its accepted class field. Representation: a Boolean in `Prop`
position is `= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a > b` is
`b < a`. The source's local lemmas of the main proof are inlined. -/

/-- If a busy-interval prefix starts with service inversion, the service
inversion, the higher-or-equal-priority interfering workload and the job's
own workload fit into `longest_busy_interval_with_pi ts tsk`. -/
theorem longest_bi_with_pi_bound_is_valid {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState],
      @work_bearing_readiness Job _ _ _ PState _ arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job] [TaskMaxNonpreemptiveSegment Task], valid_preemption_model arr_seq sched →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ SBF : SupplyBoundFunction,
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) tsk SBF.supply_bound_function →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant,
      @Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix Job _ _ _ PState arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) j t1 t2 →
    ∀ δ : duration, t1 + δ ≤ t2 →
      0 < @cumulative_service_inversion Job _ PState arr_seq sched
        (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task))) j t1 (t1 + δ) →
      @cumulative_service_inversion Job _ PState arr_seq sched
          (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task))) j t1 (t1 + δ) +
        (@cumulative_other_hep_jobs_interfering_workload Job _ _ arr_seq
            (@EDF Job _ (job_deadline_from_task_deadline Job Task)) j t1 (t1 + δ) +
          workload_of_job arr_seq j t1 (t1 + δ)) ≤
        longest_busy_interval_with_pi ts tsk := by
  intro huni hsup arr_seq hva sched _ hwb hvs _ _ hvpm hvm hresp ts hall hcost _ hrespma tsk _ SBF _
    j harr hjob hpos t1 t2 hpref δ hle hSI
  let _ : JLFP_policy Job := @EDF Job _ (job_deadline_from_task_deadline Job Task)
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true hjob
  obtain ⟨jlp, hlp_arr, hlp_nhep, hSIeq⟩ :=
    Prosa.Analysis.Facts.BusyInterval.ServiceInversion.cumulative_service_inversion_from_one_job huni hsup
      _ EDF_is_reflexive EDF_is_transitive arr_seq hva sched hwb hvs hvpm hresp j harr hpos t1 t2 hpref
      (t1 + δ) hle hSI
  have hja : t1 ≤ job_arrival j := by
    have h := hpref.2.2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  -- `jlp` is served, hence arrived in the arrival sequence
  have hlp_in : arrives_in arr_seq jlp := by
    rw [hSIeq] at hSI
    obtain ⟨t, _, hst⟩ := cumulative_service_implies_scheduled sched jlp t1 (t1 + δ) hSI
    exact hfrom jlp t hst
  -- `jlp` has a strictly later absolute deadline than `j`
  have hdl : job_arrival j + task_deadline (job_task (Task := Task) j) <
      job_arrival jlp + task_deadline (job_task (Task := Task) jlp) := by
    have h := hlp_nhep
    simp only [Bool.not_eq_true'] at h
    change decide (job_arrival jlp + task_deadline (job_task (Task := Task) jlp) ≤
      job_arrival j + task_deadline (job_task (Task := Task) j)) = false at h
    exact Nat.lt_of_not_le (of_decide_eq_false h)
  rw [hj] at hdl
  apply leq_bigmax_sup
  refine ⟨job_task (Task := Task) jlp, of_decide_eq_true (hall jlp hlp_in), decide_eq_true (by omega'), ?_⟩
  -- the service inversion is bounded by `jlp`'s last nonpreemptive segment
  have hsvc := Prosa.Analysis.Facts.BusyInterval.ServiceInversion.lp_job_bounded_service (Task := Task) huni hsup
    _ EDF_is_transitive arr_seq hva sched hwb hvs hvpm hvm hresp j harr hpos jlp hlp_in hlp_nhep t1 t2 hpref
    (t1 + δ) hle
  have hnp := of_decide_eq_true (hvm.2 jlp hlp_in).1
  -- the higher-or-equal-priority workload is bounded by the RBFs of the tasks with no later deadline
  have hwl := workload_job_and_ahep_eq_workload_hep arr_seq _ EDF_is_reflexive j t1 (t1 + δ)
  rw [cumulative_iw_hep_eq_workload_of_ohep arr_seq t1 (t1 + δ) j]
  have hhep : workload_of_hep_jobs arr_seq j t1 (t1 + δ) ≤
      sumFiltered ts
        (fun tsk_hp => decide (task_deadline tsk_hp ≤ task_deadline (job_task (Task := Task) jlp)))
        (fun tsk_hp => task_request_bound_function tsk_hp
          (task_deadline (job_task (Task := Task) jlp) - task_deadline tsk_hp)) := by
    -- weaken to the jobs with priority no lower than `jlp`
    have hweak : workload_of_hep_jobs arr_seq j t1 (t1 + δ) ≤
        workload_of_jobs (fun x => (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job x jlp)
          (arrivals_between arr_seq t1 (t1 + δ)) := by
      apply workload_of_jobs_weaken
      intro x hx
      change decide (job_arrival x + task_deadline (job_task (Task := Task) x) ≤
        job_arrival j + task_deadline (job_task (Task := Task) j)) = true at hx
      change decide (job_arrival x + task_deadline (job_task (Task := Task) x) ≤
        job_arrival jlp + task_deadline (job_task (Task := Task) jlp)) = true
      have := of_decide_eq_true hx
      rw [hj] at this
      exact decide_eq_true (by omega')
    refine Nat.le_trans hweak ?_
    -- partition by tasks
    refine Nat.le_trans (workload_of_jobs_le_sum_over_partitions
      (fun x => (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job x jlp)
      (fun tsk_hp => decide (task_deadline tsk_hp ≤ task_deadline (job_task (Task := Task) jlp)))
      (arrivals_between arr_seq t1 (t1 + δ)) ts
      (fun x hx => hall x (in_arrivals_implies_arrived arr_seq x _ _ hx))
      (fun x hx hP => by
        have hxa := job_arrival_between_ge arr_seq hva.1 x t1 (t1 + δ) hx
        change decide (job_arrival x + task_deadline (job_task (Task := Task) x) ≤
          job_arrival jlp + task_deadline (job_task (Task := Task) jlp)) = true at hP
        have := of_decide_eq_true hP
        exact decide_eq_true (by omega'))) ?_
    apply leq_sum_seq
    intro tsk_o hin_o _
    have hresp_o := hrespma tsk_o (decide_eq_true hin_o)
    have hP : ∀ x : Job, ((@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job x jlp &&
        decide (job_task (Task := Task) x = tsk_o)) = true → job_of_task tsk_o x = true := by
      intro x h; simp only [Bool.and_eq_true] at h; exact h.2
    by_cases hδo : δ ≤ task_deadline (job_task (Task := Task) jlp) - task_deadline tsk_o
    · refine Nat.le_trans (workload_of_jobs_reduce_range arr_seq t1 (t1 + δ)
        (t1 + (task_deadline (job_task (Task := Task) jlp) - task_deadline tsk_o)) _ (by omega') (by omega')) ?_
      exact rbf_spec' arr_seq hcost _ tsk_o hresp_o hP t1 _
    · rw [workload_of_jobs_nil_tail arr_seq hva.1 _ t1 (t1 + δ)
        (t1 + (task_deadline (job_task (Task := Task) jlp) - task_deadline tsk_o)) (by omega') ?_]
      · exact rbf_spec' arr_seq hcost _ tsk_o hresp_o hP t1 _
      · intro x _ hxge
        show (!((@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job x jlp &&
          decide (job_task (Task := Task) x = tsk_o))) = true
        cases hto : decide (job_task (Task := Task) x = tsk_o) with
        | false => simp
        | true =>
          have hto' : job_task (Task := Task) x = tsk_o := of_decide_eq_true hto
          simp only [Bool.and_true, Bool.not_eq_true']
          change decide (job_arrival x + task_deadline (job_task (Task := Task) x) ≤
            job_arrival jlp + task_deadline (job_task (Task := Task) jlp)) = false
          rw [hto']
          exact decide_eq_false (by omega')
  omega'

theorem busy_intervals_are_bounded_rs_edf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState],
      @work_bearing_readiness Job _ _ _ PState _ arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job] [TaskMaxNonpreemptiveSegment Task], valid_preemption_model arr_seq sched →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _
        (@rs_jlfp_interference Job _ PState arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)))
        (@rs_jlfp_interfering_workload Job _ _ PState arr_seq sched
          (@EDF Job _ (job_deadline_from_task_deadline Job Task))) _ _ _ arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ SBF : SupplyBoundFunction,
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ L : duration, 0 < L →
      longest_busy_interval_with_pi ts tsk ≤ SBF.supply_bound_function L →
      total_request_bound_function ts L ≤ SBF.supply_bound_function L →
      @busy_intervals_are_bounded_by Job _
        (@rs_jlfp_interference Job _ PState arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)))
        (@rs_jlfp_interfering_workload Job _ _ PState arr_seq sched
          (@EDF Job _ (job_deadline_from_task_deadline Job Task))) _ _ PState
        arr_seq sched Task _ _ tsk L := by
  intro huni hsup hcons arr_seq hva sched _ hwb hvs _ _ hvpm hvm hresp hwc ts hall hcost _
    hrespma tsk hin SBF hsbf hunitsbf L hL hpi hfix
  let _ : JLFP_policy Job := @EDF Job _ (job_deadline_from_task_deadline Job Task)
  let _ := rs_jlfp_interference arr_seq sched
  let _ := rs_jlfp_interfering_workload arr_seq sched
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hreflJ : reflexive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) := EDF_is_reflexive
  have hSBFle : SBF.supply_bound_function L ≤ L :=
    sbf_bounded_by_duration arr_seq sched _ hsbf hunitsbf L
  -- the workload of `j` and the interfering workload over `[t1, t1 + L)` are bounded by `L`
  have hWL : ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → 0 < job_cost j →
      ∀ t1 t2 : instant,
        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
        t1 + L ≤ t2 →
        workload_of_job arr_seq j t1 (t1 + L) + cumulative_interfering_workload j t1 (t1 + L) ≤ L := by
    intro j harr hjob hpos t1 t2 hpref hle
    have hposb : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
    rw [cumulative_interfering_workload_split arr_seq sched j t1 (t1 + L)]
    have hbl := Prosa.Analysis.Facts.SBF.blackout_during_bound_SBF hsup arr_seq sched _ hsbf j harr t1 t2
      ⟨hjob, hpref⟩ L hle
    have hwl := workload_job_and_ahep_eq_workload_hep arr_seq _ hreflJ j t1 (t1 + L)
    rw [← cumulative_iw_hep_eq_workload_of_ohep arr_seq t1 (t1 + L) j] at hwl
    rcases Nat.eq_zero_or_pos (@cumulative_service_inversion Job _ PState arr_seq sched
        (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task))) j t1 (t1 + L)) with h0 | hSI
    · have hrbf := hep_workload_le_total_rbf arr_seq hcost ts hall hrespma
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) j t1 L
      omega'
    · have hlong := longest_bi_with_pi_bound_is_valid huni hsup arr_seq hva sched hwb hvs hvpm hvm hresp ts
        hall hcost hrespma tsk hin SBF hsbf j harr hjob hposb t1 t2 hpref L hle hSI
      omega'
  intro j harr hjob hcpos
  have hpos : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hcpos
  have hpend := job_pending_at_arrival sched j hcpos hmust
  obtain ⟨t1, hle1, hpref⟩ :=
    busy_interval_prefix_exists huni hsup hcons (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task))
      hreflJ arr_seq hva sched hvs j harr hpos
  have hequiv := fun t2 => instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup hcons
    arr_seq hva sched hfrom hmust hcde (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)) hreflJ
    j harr t1 t2
  refine ⟨t1, ?_⟩
  by_cases hLpref : Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 (t1 + L)
  · -- Case 1: the busy-interval prefix continues until `t1 + L`
    have hnospec := instantiated_i_and_w_no_speculative_execution huni hsup hcons arr_seq hva sched hfrom hmust
      hcde (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)) hreflJ
    obtain ⟨t2, hlt2, hle2, hbusy⟩ := Prosa.Analysis.Abstract.BusyInterval.busy_interval_is_bounded hu hnospec
      arr_seq hva.1 hva.2 tsk sched hwc hmust hcde j harr hjob hpos (job_arrival j) hpend t1
      ((hequiv _).mp hpref) L hL (hWL j harr hjob hcpos t1 (t1 + L) hLpref (Nat.le_refl _))
    exact ⟨t2, ⟨hle1, hlt2⟩, hle2, hbusy⟩
  · -- Case 2: the busy-interval prefix terminates before `t1 + L`
    have harrL : job_arrival j < t1 + L := by
      apply Nat.lt_of_not_le
      intro hge
      have hex := workload_exceeds_interval huni hsup hcons
        (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)) hreflJ arr_seq hva sched hvs
        hwc j harr hpos t1 (job_arrival j + 1) hpref L hL (by omega')
      have hb := hWL j harr hjob hcpos t1 (job_arrival j + 1) hpref (by omega')
      omega'
    obtain ⟨t2, hbusy⟩ := Prosa.Analysis.Abstract.BusyInterval.terminating_busy_prefix_is_busy_interval sched j hpos
      t1 (job_arrival j + 1) (t1 + L) (by omega') ((hequiv _).mp hpref)
      (fun h => hLpref ((hequiv _).mpr h))
    have hcl := abstract_busy_interval_classic_busy_interval_prefix huni hsup hcons arr_seq hva sched hfrom hmust
      hcde (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)) hreflJ j harr t1 t2 hbusy
    obtain ⟨⟨_, hlt2⟩, _, _⟩ := hbusy.1
    refine ⟨t2, ⟨hle1, hlt2⟩, ?_, hbusy⟩
    apply Nat.le_of_not_lt
    intro hgt
    apply hLpref
    obtain ⟨_, hq1, hnq, _⟩ := hcl
    refine ⟨by omega', hq1, ?_, ?_⟩
    · intro t ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    · simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'

end Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Edf
