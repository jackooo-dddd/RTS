-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/transfer_schedulability/paper_model.v

import Prosa.Util.All
import Prosa.Analysis.Definitions.FinishTime
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Facts.Behavior.Arrivals
import Prosa.Results.TransferSchedulability.Criterion

namespace Prosa.Results.TransferSchedulability.PaperModel

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Definitions.FinishTime
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Results.TransferSchedulability.Criterion

/-! The EMSOFT'25 system model (job precedence and delays, system evolutions, schedulers) and the transfer
schedulability results stated for it.

Binders follow the elaborated source types. In particular:
- `Scheduler` keeps the source's elaborated signature: its `{JobPredecessors}` and `{SystemEvolutions Omega}`
  instance binders introduce their own job types `Job0`, `Job1`; at every use they are the model's `Job`.
- The section's `#[local] Existing Instance ideal.processor_state` and `Let PState` are the accepted
  `processor_state Job`; the `Let`s `job_cost omega`, `job_delay omega` and `job_ready omega` are inlined as
  `evo_costs omega`, `evo_delays omega` and `delayed_precedence_ready_instance` at them, passed explicitly where the
  elaborated statements use them implicitly.
- The source's `#[local, program] Instance delayed_precedence_ready_instance` (no public declaration, but the
  statements use it) is a definition, with its `Let`s `delay_has_passed` and `is_released` inlined.
- The non-starvation hypotheses `{R : duration | P R}` are Lean subtypes `{R : duration // P R = true}`, `sval` is
  `Subtype.val` and `proj2_sig` is `Subtype.property`.
- The section-local `R` / `ref_response_time_bound` / `online_response_time_bound` `Let`s are inlined.
Representation: a Boolean in `Prop` position is `= true`; `t >= delta` is `decide (delta ≤ t)`; `all p xs` is
`xs.all p`; `a <= b` as a Boolean is `decide (a ≤ b)`; `~~ b` is `!b`. -/

/-! ## Elements of the EMSOFT'25 system model -/

/-- The predecessors of each job. -/
class JobPredecessors (Job : JobType) [DecidableEq Job] where
  job_predecessors : Job → List Job

/-- The delay between the completion of a predecessor and the start of a job. -/
class JobDelay (Job : JobType) [DecidableEq Job] where
  job_delay : Job → Job → duration

export JobPredecessors (job_predecessors)
export JobDelay (job_delay)

/-- Readiness under delayed precedence constraints: a job is ready if it has arrived, every predecessor completed at
least the corresponding delay earlier, and it is not yet complete. -/
@[reducible] noncomputable def delayed_precedence_ready_instance {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    [JobArrival Job] [JobCost Job] [JobPredecessors Job] [JobDelay Job] : JobReady Job PState where
  job_ready sched j t :=
    (decide (job_arrival j ≤ t) &&
      (job_predecessors j).all (fun j_pred =>
        decide (job_delay j j_pred ≤ t) && completed_by sched j_pred (t - job_delay j j_pred)))
    && !completed_by sched j t
  ready_implies_pending := by
    intro sched j t h
    simp only [Bool.and_eq_true] at h
    simp only [pending, has_arrived, Bool.and_eq_true]
    exact ⟨h.1.1, h.2⟩

/-- System evolutions determine the job costs and the delays. -/
class SystemEvolutions (Omega : Type) (Job : JobType) [DecidableEq Job] where
  evo_costs : Omega → JobCost Job
  evo_delays : Omega → JobDelay Job

export SystemEvolutions (evo_costs evo_delays)

/-- A scheduler maps each system evolution to a schedule. -/
def Scheduler (Omega : Type) (Job : JobType) [DecidableEq Job] (PState : ProcessorState Job)
    (_ : JobArrival Job) (Job0 : JobType) [DecidableEq Job0] (_ : JobPredecessors Job0)
    (Job1 : JobType) [DecidableEq Job1] (_ : SystemEvolutions Omega Job1) :=
  Omega → schedule PState

/-! ## The EMSOFT'25 model instantiated -/

/-- Schedulability is transferred from the reference schedule `algA omega_0` to the online schedule `algB omega`. -/
def schedulability_transferred_AB {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega)
    (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE) (omega : Omega) : Prop :=
  schedulability_transferred (algA omega_0) (algB omega) (evo_costs omega_0) (evo_costs omega)

/-- The clairvoyant transfer criterion (w.r.t. online job costs). -/
def clairvoyant_criterion {Job : JobType} [DecidableEq Job] [hA : JobArrival Job] [hP : JobPredecessors Job]
    (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega)
    (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE) : Prop :=
  ∀ omega : Omega, transfer_schedulability_criterion (algA omega_0) (algB omega)
    (evo_costs omega_0) (evo_costs omega) arr_seq (evo_costs omega)

/-- LEAN_HELPER: a valid schedule (w.r.t. the readiness model of an evolution) lets completed jobs not execute and
jobs execute only after their arrival. -/
private theorem valid_facts {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobPredecessors Job]
    (arr_seq : arrival_sequence Job) (c : JobCost Job) (d : JobDelay Job)
    (sched : schedule (processor_state Job))
    (hv : @valid_schedule Job _ _ (processor_state Job) sched c
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ c _ d) arr_seq) :
    @completed_jobs_dont_execute Job _ _ sched c ∧ jobs_must_arrive_to_execute sched :=
  ⟨@valid_schedule_implies_completed_jobs_dont_execute Job _ _ sched c _
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ c _ d) arr_seq hv,
   @valid_schedule_implies_jobs_must_arrive_to_execute Job _ _ sched c _
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ c _ d) arr_seq hv⟩

/-- The clairvoyant criterion ensures that schedulability is transferred in every evolution. -/
theorem clairvoyant_sufficiency {Job : JobType} [DecidableEq Job] [hA : JobArrival Job] [hP : JobPredecessors Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega),
      (∀ (omega : Omega) (j : Job), @job_cost Job _ (evo_costs omega) j ≤ @job_cost Job _ (evo_costs omega_0) j) →
      ∀ algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE,
        @valid_schedule Job _ _ (processor_state Job) (algA omega_0) (evo_costs omega_0)
          (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega_0) _
            (evo_delays omega_0)) arr_seq →
        (∀ omega : Omega, @valid_schedule Job _ _ (processor_state Job) (algB omega) (evo_costs omega)
          (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega) _
            (evo_delays omega)) arr_seq) →
        clairvoyant_criterion arr_seq Omega omega_0 algA algB →
        ∀ omega : Omega, schedulability_transferred_AB Omega omega_0 algA algB omega := by
  intro hva Omega _ omega_0 hmax algA algB hA0 hB hcrit omega
  obtain ⟨hcdeA, harrA⟩ := valid_facts arr_seq _ _ _ hA0
  obtain ⟨hcdeB, _⟩ := valid_facts arr_seq _ _ _ (hB omega)
  exact online_transfer_schedulability_criterion_sufficiency (algA omega_0) (algB omega)
    (evo_costs omega_0) (evo_costs omega) arr_seq hva hA0.1 harrA hcdeA hcdeB (hmax omega) (hcrit omega)

/-- Conversely, schedulability transferred in every evolution implies the clairvoyant criterion. -/
theorem clairvoyant_necessity {Job : JobType} [DecidableEq Job] [hA : JobArrival Job] [hP : JobPredecessors Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega)
      (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE),
      (∀ omega : Omega, @valid_schedule Job _ _ (processor_state Job) (algB omega) (evo_costs omega)
        (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega) _
          (evo_delays omega)) arr_seq) →
      (∀ omega : Omega, schedulability_transferred_AB Omega omega_0 algA algB omega) →
      clairvoyant_criterion arr_seq Omega omega_0 algA algB := by
  intro hva Omega _ omega_0 algA algB hB htrans omega
  obtain ⟨hcdeB, _⟩ := valid_facts arr_seq _ _ _ (hB omega)
  exact online_transfer_schedulability_criterion_necessity (algA omega_0) (algB omega)
    (evo_costs omega_0) (evo_costs omega) arr_seq hva hcdeB (htrans omega)

/-- The non-clairvoyant transfer criterion (w.r.t. reference job costs). -/
def nonclairvoyant_criterion {Job : JobType} [DecidableEq Job] [hA : JobArrival Job] [hP : JobPredecessors Job]
    (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega)
    (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE) : Prop :=
  ∀ omega : Omega, transfer_schedulability_criterion (algA omega_0) (algB omega)
    (evo_costs omega_0) (evo_costs omega) arr_seq (evo_costs omega_0)

/-- The non-clairvoyant criterion ensures that schedulability is transferred in every evolution. -/
theorem nonclairvoyant_sufficiency {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega),
      (∀ (omega : Omega) (j : Job), @job_cost Job _ (evo_costs omega) j ≤ @job_cost Job _ (evo_costs omega_0) j) →
      ∀ algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE,
        @valid_schedule Job _ _ (processor_state Job) (algA omega_0) (evo_costs omega_0)
          (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega_0) _
            (evo_delays omega_0)) arr_seq →
        (∀ omega : Omega, @valid_schedule Job _ _ (processor_state Job) (algB omega) (evo_costs omega)
          (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega) _
            (evo_delays omega)) arr_seq) →
        nonclairvoyant_criterion arr_seq Omega omega_0 algA algB →
        ∀ omega : Omega, schedulability_transferred_AB Omega omega_0 algA algB omega := by
  intro hva Omega _ omega_0 hmax algA algB hA0 hB hcrit omega
  obtain ⟨hcdeA, harrA⟩ := valid_facts arr_seq _ _ _ hA0
  obtain ⟨hcdeB, _⟩ := valid_facts arr_seq _ _ _ (hB omega)
  exact ref_transfer_schedulability_criterion_sufficiency (algA omega_0) (algB omega)
    (evo_costs omega_0) (evo_costs omega) arr_seq hva hA0.1 harrA hcdeA hcdeB (hmax omega) (hcrit omega)

/-! ## Results w.r.t. finish times -/

/-- The finish time of `jf` in the reference schedule. -/
noncomputable def ref_finish_time {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (omega_0 : Omega) (algA : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (jf : Job) (H_arrives : arrives_in arr_seq jf) : instant :=
  @finish_time Job _ _ (evo_costs omega_0) _ (algA omega_0) jf (H_non_starvation jf H_arrives).val
    (H_non_starvation jf H_arrives).property

/-- Under schedulability transfer, the reference bound is also a response-time bound in the online schedule. -/
theorem online_response_time_bound {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (omega_0 : Omega) (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (omega : Omega) (jf : Job) (H_arrives : arrives_in arr_seq jf) :
    schedulability_transferred_AB Omega omega_0 algA algB omega →
      @job_response_time_bound Job _ _ (algB omega) (evo_costs omega) _ jf (H_non_starvation jf H_arrives).val =
        true :=
  fun H_trans => H_trans jf _ (H_non_starvation jf H_arrives).property

/-- The finish time of `jf` in the online schedule (under schedulability transfer). -/
noncomputable def online_finish_time {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (omega_0 : Omega) (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (omega : Omega) (jf : Job) (H_arrives : arrives_in arr_seq jf)
    (H_trans : schedulability_transferred_AB Omega omega_0 algA algB omega) : instant :=
  @finish_time Job _ _ (evo_costs omega) _ (algB omega) jf (H_non_starvation jf H_arrives).val
    (online_response_time_bound arr_seq Omega omega_0 algA algB H_non_starvation omega jf H_arrives H_trans)

/-- The online finish time is no later than the reference finish time. -/
noncomputable def online_finish_time_bounded {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (omega_0 : Omega) (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (omega : Omega) (jf : Job) (H_arrives : arrives_in arr_seq jf)
    (H_trans : schedulability_transferred_AB Omega omega_0 algA algB omega) : Bool :=
  decide (online_finish_time arr_seq Omega omega_0 algA algB H_non_starvation omega jf H_arrives H_trans ≤
    ref_finish_time arr_seq Omega omega_0 algA H_non_starvation jf H_arrives)

/-- LEAN_HELPER: completion transfers, hence the online finish time is at most the reference one. -/
private theorem finish_time_bounded_of_trans {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (omega_0 : Omega) (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (omega : Omega) (j : Job) (IN : arrives_in arr_seq j)
    (H_trans : schedulability_transferred_AB Omega omega_0 algA algB omega) :
    online_finish_time_bounded arr_seq Omega omega_0 algA algB H_non_starvation omega j IN H_trans = true := by
  unfold online_finish_time_bounded
  refine decide_eq_true ?_
  exact @earliest_finish_time Job _ _ (evo_costs omega) _ (algB omega) j _ _ _
    (H_trans j _ (@finished_at_finish_time Job _ _ (evo_costs omega_0) _ (algA omega_0) j _ _))

/-- Clairvoyant sufficiency w.r.t. finish times. -/
theorem clairvoyant_sufficiency' {Job : JobType} [DecidableEq Job] [hA : JobArrival Job] [hP : JobPredecessors Job]
    (arr_seq : arrival_sequence Job) (H_valid_arrivals : valid_arrival_sequence arr_seq) (Omega : Type)
    [hE : SystemEvolutions Omega Job] (omega_0 : Omega)
    (H_max_cost : ∀ (omega : Omega) (j : Job),
      @job_cost Job _ (evo_costs omega) j ≤ @job_cost Job _ (evo_costs omega_0) j)
    (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_well_formed_A : @valid_schedule Job _ _ (processor_state Job) (algA omega_0) (evo_costs omega_0)
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega_0) _
        (evo_delays omega_0)) arr_seq)
    (H_well_formed_B : ∀ omega : Omega, @valid_schedule Job _ _ (processor_state Job) (algB omega) (evo_costs omega)
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega) _
        (evo_delays omega)) arr_seq)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (H_criterion : clairvoyant_criterion arr_seq Omega omega_0 algA algB) (omega : Omega) (j : Job)
    (IN : arrives_in arr_seq j) :
    online_finish_time_bounded arr_seq Omega omega_0 algA algB H_non_starvation omega j IN
      (clairvoyant_sufficiency arr_seq H_valid_arrivals Omega omega_0 H_max_cost algA algB H_well_formed_A
        H_well_formed_B H_criterion omega) = true :=
  finish_time_bounded_of_trans arr_seq Omega omega_0 algA algB H_non_starvation omega j IN _

/-- Non-clairvoyant sufficiency w.r.t. finish times. -/
theorem nonclairvoyant_sufficiency' {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (H_valid_arrivals : valid_arrival_sequence arr_seq)
    (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega)
    (H_max_cost : ∀ (omega : Omega) (j : Job),
      @job_cost Job _ (evo_costs omega) j ≤ @job_cost Job _ (evo_costs omega_0) j)
    (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_well_formed_A : @valid_schedule Job _ _ (processor_state Job) (algA omega_0) (evo_costs omega_0)
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega_0) _
        (evo_delays omega_0)) arr_seq)
    (H_well_formed_B : ∀ omega : Omega, @valid_schedule Job _ _ (processor_state Job) (algB omega) (evo_costs omega)
      (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega) _
        (evo_delays omega)) arr_seq)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (H_criterion : nonclairvoyant_criterion arr_seq Omega omega_0 algA algB) (omega : Omega) (j : Job)
    (IN : arrives_in arr_seq j) :
    online_finish_time_bounded arr_seq Omega omega_0 algA algB H_non_starvation omega j IN
      (nonclairvoyant_sufficiency arr_seq H_valid_arrivals Omega omega_0 H_max_cost algA algB H_well_formed_A
        H_well_formed_B H_criterion omega) = true :=
  finish_time_bounded_of_trans arr_seq Omega omega_0 algA algB H_non_starvation omega j IN _

/-- The online finish time, under the strengthened non-starvation assumption. -/
noncomputable def online_finish_time' {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation' : ∀ j : Job, arrives_in arr_seq j → ∀ omega : Omega,
      {R : duration // @job_response_time_bound Job _ _ (algB omega) (evo_costs omega) _ j R = true})
    (omega : Omega) (jf : Job) (H_arrives : arrives_in arr_seq jf) : instant :=
  @finish_time Job _ _ (evo_costs omega) _ (algB omega) jf (H_non_starvation' jf H_arrives omega).val
    (H_non_starvation' jf H_arrives omega).property

/-- The online finish time is no later than the reference finish time. -/
noncomputable def online_finish_time_bounded' {Job : JobType} [DecidableEq Job] [hA : JobArrival Job]
    [hP : JobPredecessors Job] (arr_seq : arrival_sequence Job) (Omega : Type) [hE : SystemEvolutions Omega Job]
    (omega_0 : Omega) (algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE)
    (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
      {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
    (H_non_starvation' : ∀ j : Job, arrives_in arr_seq j → ∀ omega : Omega,
      {R : duration // @job_response_time_bound Job _ _ (algB omega) (evo_costs omega) _ j R = true})
    (omega : Omega) (jf : Job) (H_arrives : arrives_in arr_seq jf) : Bool :=
  decide (online_finish_time' arr_seq Omega algB H_non_starvation' omega jf H_arrives ≤
    ref_finish_time arr_seq Omega omega_0 algA H_non_starvation jf H_arrives)

/-- Clairvoyant necessity w.r.t. finish times. -/
theorem clairvoyant_necessity' {Job : JobType} [DecidableEq Job] [hA : JobArrival Job] [hP : JobPredecessors Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (Omega : Type) [hE : SystemEvolutions Omega Job] (omega_0 : Omega),
      (∀ (omega : Omega) (j : Job), @job_cost Job _ (evo_costs omega) j ≤ @job_cost Job _ (evo_costs omega_0) j) →
      ∀ algA algB : Scheduler Omega Job (processor_state Job) hA Job hP Job hE,
        @valid_schedule Job _ _ (processor_state Job) (algA omega_0) (evo_costs omega_0)
          (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega_0) _
            (evo_delays omega_0)) arr_seq →
        (∀ omega : Omega, @valid_schedule Job _ _ (processor_state Job) (algB omega) (evo_costs omega)
          (@delayed_precedence_ready_instance Job _ (processor_state Job) _ (evo_costs omega) _
            (evo_delays omega)) arr_seq) →
        ∀ (H_non_starvation : ∀ j : Job, arrives_in arr_seq j →
            {R : duration // @job_response_time_bound Job _ _ (algA omega_0) (evo_costs omega_0) _ j R = true})
          (H_non_starvation' : ∀ j : Job, arrives_in arr_seq j → ∀ omega : Omega,
            {R : duration // @job_response_time_bound Job _ _ (algB omega) (evo_costs omega) _ j R = true}),
          (∀ (omega : Omega) (j : Job) (in_arrival_sequence : arrives_in arr_seq j),
            online_finish_time_bounded' arr_seq Omega omega_0 algA algB H_non_starvation H_non_starvation' omega j
              in_arrival_sequence = true) →
          clairvoyant_criterion arr_seq Omega omega_0 algA algB := by
  intro hva Omega _ omega_0 hmax algA algB hA0 hB H_non_starvation H_non_starvation' H_bounded
  refine clairvoyant_necessity arr_seq hva Omega omega_0 algA algB hB ?_
  intro omega j t hcomp
  by_cases hzero : @job_cost Job _ (evo_costs omega_0) j = 0
  · -- a job of cost zero in the reference evolution has cost zero online, hence is complete
    have h0 : @job_cost Job _ (evo_costs omega) j = 0 := Nat.eq_zero_of_le_zero (hzero ▸ hmax omega j)
    simp only [completed_by, h0, decide_eq_true_eq]
    exact Nat.zero_le _
  · -- a job of positive reference cost completed at `t` was scheduled before `t`, so it arrived
    have hpos : 0 < service (algA omega_0) j t := by
      have hc := hcomp
      simp only [completed_by, decide_eq_true_eq] at hc
      dsimp only [work, instant] at *
      omega
    obtain ⟨t', _, hsched⟩ := positive_service_implies_scheduled_before (algA omega_0) j t hpos
    have IN : arrives_in arr_seq j := hA0.1 j t' hsched
    have hbound := H_bounded omega j IN
    unfold online_finish_time_bounded' at hbound
    have hle := of_decide_eq_true hbound
    have hft : online_finish_time' arr_seq Omega algB H_non_starvation' omega j IN ≤ t :=
      Nat.le_trans hle (@earliest_finish_time Job _ _ (evo_costs omega_0) _ (algA omega_0) j _ _ t hcomp)
    exact @completion_monotonic Job _ (evo_costs omega) _ (algB omega) j _ t hft
      (@finished_at_finish_time Job _ _ (evo_costs omega) _ (algB omega) j _ _)

end Prosa.Results.TransferSchedulability.PaperModel
