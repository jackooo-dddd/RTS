From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduleChange ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ScheduleChangeBaseAdapter ScheduleChangeStateAdapter
  ScheduleChangeOptionOperations ScheduleChangeIntervalOperations
  ScheduleChangeListOperations.

(** The only input relation is the pointwise Overheads schedule relation;
    [sc_schedule_canonical] constructs one for every source schedule. *)

Lemma sc_option_eq_bool_correspondence (Job : eqType)
    (aR bR : option Job)
    (aL bL : ImportedScheduleChange.Option Job) :
  ScOptionRel aR aL -> ScOptionRel bR bL ->
  ScBoolRel (aR == bR)
    (ImportedScheduleChange.Decidable_decide (Lean.eq aL bL)
      (ImportedScheduleChange.Option_instDecidableEq Job
        (sc_decidable_eq Job) aL bL)).
Proof.
  intros Ha Hb. apply sc_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP=> Heq. exact (prop_to_sprop _ _
      (sc_option_eq_correspondence Job aR bR aL bL Ha Hb) Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _
      (sc_option_eq_correspondence Job aR bR aL bL Ha Hb) Heq).
Qed.

Lemma sc_nat_eq_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ScBoolRel (aR == bR)
    (ImportedScheduleChange.Decidable_decide (Lean.eq aL bL)
      (ImportedScheduleChange.instDecidableEqNat aL bL)).
Proof.
  intros Ha Hb. apply sc_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP=> Heq. exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb) Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb) Heq).
Qed.

Section TargetCorrespondences.
  Context (Job : eqType).
  Context (schedR : ScSourceSchedule Job).
  Context (schedL : ScTargetSchedule Job).
  Hypothesis Hsched : ScScheduleRel Job schedR schedL.

  Lemma schedule_change_correspondence tR tL :
    SubNatRel tR tL ->
    ScBoolRel
      (@prosa.analysis.definitions.overheads.schedule_change.schedule_change
        Job schedR tR)
      (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change
        Job (sc_decidable_eq Job) schedL tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.overheads.schedule_change.schedule_change,
      ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change.
    have Hpred := sc_target_pred_related tR tL Ht.
    have Hprev := sc_scheduled_job_correspondence Job schedR schedL
      tR.-1 (ImportedScheduleChange.Nat_pred tL) Hsched Hpred.
    have Hcur := sc_scheduled_job_correspondence Job schedR schedL
      tR tL Hsched Ht.
    apply sc_decide_bool_correspondence.
    exact (sc_option_ne_correspondence Job _ _ _ _ Hprev Hcur).
  Qed.

  Lemma number_schedule_changes_correspondence t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes
        Job schedR t1R t2R)
      (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes
        Job (sc_decidable_eq Job) schedL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    unfold prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes,
      ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes.
    apply sc_countP_related.
    - move=> nR nL Hn. exact (schedule_change_correspondence nR nL Hn).
    - exact (sc_index_iota_related t1R t1L t2R t2L Ht1 Ht2).
  Qed.

  Lemma no_schedule_changes_during_correspondence t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    ScBoolRel
      (@prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during
        Job schedR t1R t2R)
      (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during
        Job (sc_decidable_eq Job) schedL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    unfold prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during,
      ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during.
    have Ht1s := sc_target_succ_related t1R t1L Ht1.
    have Hcount := number_schedule_changes_correspondence
      t1R.+1 (sc_target_add t1L sc_target_one) t2R t2L Ht1s Ht2.
    exact (sc_nat_eq_bool_correspondence _ _ 0 Lean.Nat_zero
      Hcount (sub_nat_rel_canonical 0)).
  Qed.

  Lemma scheduled_job_invariant_correspondence
      (ojR : option Job) (ojL : ImportedScheduleChange.Option Job)
      t1R t1L t2R t2L :
    ScOptionRel ojR ojL ->
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    ScBoolRel
      (@prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant
        Job schedR ojR t1R t2R)
      (ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant
        Job (sc_decidable_eq Job) schedL ojL t1L t2L).
  Proof.
    intros Hoj Ht1 Ht2.
    unfold prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant,
      ImportedScheduleChange.Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant.
    apply sc_all_related.
    - move=> nR nL Hn.
      have Hscheduled := sc_scheduled_job_correspondence Job schedR schedL
        nR nL Hsched Hn.
      exact (sc_option_eq_bool_correspondence Job _ _ _ _ Hscheduled Hoj).
    - exact (sc_index_iota_related t1R t1L t2R t2L Ht1 Ht2).
  Qed.
End TargetCorrespondences.
