From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From HB Require Import structures.
From prosa Require Import implementation.definitions.task behavior.all model.processor.ideal
  implementation.definitions.generic_scheduler implementation.definitions.ideal_uni_scheduler util.supremum
  model.schedule.work_conserving model.schedule.preemption_time model.schedule.priority_driven
  model.preemption.parameter analysis.transform.swap model.priority.classes.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFPSched ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  PsEac PsAb PsImplTask PsListOps PsSvcBase PsSvcNatBool PsSvcInterval.

Module I := ImportedRefEDFPSched.
Module T := prosa.implementation.definitions.task.

(** Job-relational correspondences of the ideal-uniprocessor scheduler stack, for the
    implementation/refinements/{EDF,FP}/{preemptive,nonpreemptive}_sched.v files.

    These files fix the job type to the concrete jobs on both sides: the source side is the Prosa
    definitions at [T.concrete_job], the target side the concrete (universe-0) copies of the compiled
    Lean definitions at the compiled [concrete_job] with its derived equality.  Jobs are related by the
    accepted fieldwise canonical relation [ItJobRel] (the graph of the accepted export map, with two-way
    totals); optional jobs by the constructor-preserving map; job lists by mapping the export and then
    the accepted list relation [ArListRel] (so the accepted membership and uniqueness certificates apply
    at the compiled job type, which carries the equality type transported along the accepted import
    map); arrival sequences and schedules pointwise.  The proofs follow the accepted
    ideal-uniprocessor-scheduler, preemption-aware and priority-aware certificates, with the identity
    job carrier replaced by [ItJobRel]; the concrete copies are closed by the concrete-job instances of
    the accepted interface equations exported with this artifact.  The readiness model, the
    preemption model and the priority policy are parameters, related by hypotheses that the per-file
    certificates discharge for their fixed instances.  No source or target theorem is used. *)

Notation LJ := I.Prosa_Implementation_Definitions_Task_concrete_job.
Notation LT := I.Prosa_Implementation_Definitions_Task_concrete_task.
Notation dJ := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job.
Notation dT := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task.
Notation JR := T.concrete_job.
Notation PSR := (prosa.model.processor.ideal.processor_state T.concrete_job).
Notation PSL := (I.Prosa_Model_Processor_Ideal_processor_state_inst1 LJ dJ).
Notation StL := (I.Prosa_Behavior_Schedule_ProcessorState_State_inst7 LJ dJ PSL).
Notation SchedR := (prosa.behavior.schedule.schedule PSR).
Notation SchedL := (I.Prosa_Behavior_Schedule_schedule_inst7 LJ dJ PSL).
Notation jcL := I.Prosa_Implementation_Definitions_Task_JobCost.
Notation jaL := I.Prosa_Implementation_Definitions_Task_JobArrival.

(** ** Generic relational combinators (restated from the accepted facts/job_constructor certificate) *)

Lemma sc_forall_cover {A B : Type} (R : A -> B -> SProp) (toL : A -> B) (toR : B -> A)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a, R a (toL a)) -> (forall b, R (toR b) b) ->
  (forall a b, R a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intros HL HR HP. apply prop_sprop_rel_intro.
  - intros H b. exact (prop_to_sprop _ _ (HP _ _ (HR b)) (H (toR b))).
  - intro H. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (HP _ _ (HL a)) (H (toL a))).
Qed.

Lemma sc_imp {P P' : Prop} {Q Q' : SProp} :
  PropSPropRel P Q -> PropSPropRel P' Q' -> PropSPropRel (P -> P') (Q -> Q').
Proof.
  intros H H'. apply prop_sprop_rel_intro.
  - intros f q. exact (prop_to_sprop _ _ H' (f (sprop_to_prop _ _ H q))).
  - intro f. apply strictly_inhabits. intro p. exact (sprop_to_prop _ _ H' (f (prop_to_sprop _ _ H p))).
Qed.

Lemma sc_and {P P' : Prop} {Q Q' : SProp} :
  PropSPropRel P Q -> PropSPropRel P' Q' -> PropSPropRel (P /\ P') (Lean.And Q Q').
Proof.
  intros H H'. apply prop_sprop_rel_intro.
  - intros [p p']. exact (Lean.And_intro _ _ (prop_to_sprop _ _ H p) (prop_to_sprop _ _ H' p')).
  - intros [q q']. apply strictly_inhabits. exact (conj (sprop_to_prop _ _ H q) (sprop_to_prop _ _ H' q')).
Qed.

Lemma sc_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall n, PR n) (forall n, PL n).
Proof.
  apply (sc_forall_cover SubNatRel sub_nat_to_imported sub_nat_to_rocq).
  - exact sub_nat_rel_canonical.
  - intro n. exact (sub_nat_imported_roundtrip n).
Qed.

Lemma sc_forall_job (PR : JR -> Prop) (PL : LJ -> SProp) :
  (forall jR jL, ItJobRel jR jL -> PropSPropRel (PR jR) (PL jL)) ->
  PropSPropRel (forall j, PR j) (forall j, PL j).
Proof.
  apply (sc_forall_cover ItJobRel it_job_export it_job_import PR PL concrete_job_source_total
    concrete_job_target_total).
Qed.

Lemma sc_exists_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists n, PR n) (I.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [n p]. exact (I.Exists_intro _ _ (sub_nat_to_imported n)
      (prop_to_sprop _ _ (HP _ _ (sub_nat_rel_canonical n)) p)).
  - intros [nL q]. apply strictly_inhabits. exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _ (HP _ _ (sub_nat_imported_roundtrip nL)) q).
Qed.

Lemma sc_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma sc_src_transport {A : Type} (P : A -> SProp) (x y : A) :
  Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma sc_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

(** ** The compiled concrete job type as an equality type (transported along the accepted import map) *)

Lemma sc_job_cancel : cancel it_job_import it_job_export.
Proof. move=> b. exact (imported_eq_to_coq_eq _ _ (it_job_target_roundtrip b)). Qed.

HB.instance Definition _ := Equality.copy I.Prosa_Implementation_Definitions_Task_concrete_job
  (can_type sc_job_cancel).

Lemma sc_job_export_inj : injective it_job_export.
Proof. exact (can_inj it_job_source_roundtrip). Qed.

Lemma sc_job_rel_eq jR jL : ItJobRel jR jL -> Logic.eq (it_job_export jR) jL.
Proof. intro H. exact (imported_eq_to_coq_eq _ _ H). Qed.

(** ** Optional jobs *)

Definition sc_opt (o : option JR) : I.Option_inst1 LJ :=
  match o with
  | None => I.Option_none_inst1 LJ
  | Some j => I.Option_some_inst1 LJ (it_job_export j)
  end.

Definition sc_opt_import (o : I.Option_inst1 LJ) : option JR :=
  match o with
  | I.Option_none_inst1 => None
  | I.Option_some_inst1 j => Some (it_job_import j)
  end.

Definition JOptRel (oR : option JR) (oL : I.Option_inst1 LJ) : SProp := Lean.eq (sc_opt oR) oL.

Lemma sc_opt_source_roundtrip o : Logic.eq (sc_opt_import (sc_opt o)) o.
Proof. case: o => [j|] //=. by rewrite it_job_source_roundtrip. Qed.

Lemma sc_opt_target_roundtrip o : JOptRel (sc_opt_import o) o.
Proof.
  destruct o as [|j]; cbn; first exact (@Lean.eq_refl _ _).
  exact (sub_imported_eq_congr (I.Option_some_inst1 LJ) _ _ (it_job_target_roundtrip j)).
Qed.

Lemma sc_opt_some_eq (sR : option JR) sL (jR : JR) jL :
  JOptRel sR sL -> ItJobRel jR jL ->
  PropSPropRel (is_true (sR == Some jR)) (Lean.eq sL (I.Option_some_inst1 LJ jL)).
Proof.
  intros Hs Hj. rewrite -(imported_eq_to_coq_eq _ _ Hs) -(imported_eq_to_coq_eq _ _ Hj).
  apply prop_sprop_rel_intro.
  - move=> /eqP ->. exact (@Lean.eq_refl _ _).
  - intro H. apply strictly_inhabits. have Hc := f_equal sc_opt_import (imported_eq_to_coq_eq _ _ H).
    rewrite sc_opt_source_roundtrip /= it_job_source_roundtrip in Hc.
    by rewrite Hc eqxx.
Qed.

Lemma sc_opt_eq (xR yR : option JR) xL yL :
  JOptRel xR xL -> JOptRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. rewrite -(imported_eq_to_coq_eq _ _ Hx) -(imported_eq_to_coq_eq _ _ Hy).
  apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - intro H. apply strictly_inhabits. have Hc := f_equal sc_opt_import (imported_eq_to_coq_eq _ _ H).
    by rewrite !sc_opt_source_roundtrip in Hc.
Qed.

(** ** Ideal states *)

Section SrcIdeal.
  Local Transparent prosa.behavior.schedule.scheduled_on prosa.behavior.schedule.service_on
    prosa.behavior.schedule.supply_on.

  Lemma sc_src_scheduled_on (j : JR) (s : option JR) (c : unit) :
    @prosa.behavior.schedule.scheduled_on JR PSR j s c = (s == Some j).
  Proof. by []. Qed.

  Lemma sc_src_scheduled_in (j : JR) (s : option JR) :
    @prosa.behavior.schedule.scheduled_in JR PSR j s = (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.scheduled_in.
    apply/existsP/idP => [[c]|H].
    - by rewrite sc_src_scheduled_on.
    - by exists tt; rewrite sc_src_scheduled_on.
  Qed.

  Lemma sc_src_service_in (j : JR) (s : option JR) :
    @prosa.behavior.schedule.service_in JR PSR j s = nat_of_bool (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.service_in (big_pred1 tt) /=.
    all: try by case: (s == Some j).
    all: by case.
  Qed.
End SrcIdeal.

Lemma sc_scheduled_in_related (jR : JR) jL (sR : option JR) sL :
  ItJobRel jR jL -> JOptRel sR sL ->
  SvcBoolRel (@prosa.behavior.schedule.scheduled_in JR PSR jR sR)
    (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst7 LJ dJ PSL jL sL).
Proof.
  intros Hj Hs. rewrite sc_src_scheduled_in.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
    (I.Prosa_Validation_RefSchedInterface_production_ideal_scheduled_in_job jL sL))).
  cbn. apply svc_decide_bool_correspondence. exact (sc_opt_some_eq _ _ _ _ Hs Hj).
Qed.

Lemma sc_service_in_related (jR : JR) jL (sR : option JR) sL :
  ItJobRel jR jL -> JOptRel sR sL ->
  SubNatRel (@prosa.behavior.schedule.service_in JR PSR jR sR)
    (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst7 LJ dJ PSL jL sL).
Proof.
  intros Hj Hs. rewrite sc_src_service_in.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
    (I.Prosa_Validation_RefSchedInterface_production_ideal_service_in_job jL sL))).
  have Hb := svc_decide_bool_correspondence _ _
    (I.Option_instDecidableEq_inst1 LJ dJ sL (I.Option_some_inst1 LJ jL)) (sc_opt_some_eq _ _ _ _ Hs Hj).
  cbn. revert Hb.
  generalize (I.Decidable_decide (Lean.eq sL (I.Option_some_inst1 LJ jL))
    (I.Option_instDecidableEq_inst1 LJ dJ sL (I.Option_some_inst1 LJ jL))).
  intros bL Hb. unfold SvcBoolRel in Hb. destruct Hb.
  change (opt_eq sR (Some jR)) with (sR == Some jR).
  destruct (sR == Some jR); cbn; [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
Qed.

(** ** Schedules *)

Definition JSchedRel (sR : SchedR) (sL : SchedL) : SProp :=
  forall tR tL, SubNatRel tR tL -> JOptRel (sR tR) (sL tL).

Section Sched.
  Variable sR : SchedR.
  Variable sL : SchedL.
  Hypothesis Hs : JSchedRel sR sL.

  Lemma sc_scheduled_at_related (jR : JR) jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (prosa.behavior.service.scheduled_at sR jR tR)
      (I.Prosa_Behavior_Service_scheduled_at_inst7 LJ dJ PSL sL jL tL).
  Proof.
    intros Hj Ht. unfold prosa.behavior.service.scheduled_at.
    cbn [I.Prosa_Behavior_Service_scheduled_at_inst7].
    exact (sc_scheduled_in_related _ _ _ _ Hj (Hs _ _ Ht)).
  Qed.

  Lemma sc_service_at_fun (jR : JR) jL : ItJobRel jR jL ->
    SvcNatFunRel (fun t => prosa.behavior.service.service_at sR jR t)
      (fun t => I.Prosa_Validation_ServiceInterface_serviceAtProjection_inst7 LJ dJ PSL sL jL t).
  Proof.
    intros Hj tR tL Ht. unfold prosa.behavior.service.service_at.
    exact (sc_service_in_related _ _ _ _ Hj (Hs _ _ Ht)).
  Qed.

  Lemma sc_service_related (jR : JR) jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SubNatRel (prosa.behavior.service.service sR jR tR)
      (I.Prosa_Behavior_Service_service_inst7 LJ dJ PSL sL jL tL).
  Proof.
    intros Hj Ht.
    exact (svc_interval_sum_related O tR _ tL _ _ (sub_nat_rel_canonical O) Ht (sc_service_at_fun _ _ Hj)).
  Qed.

  Lemma sc_completed_by_related (jR : JR) jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (prosa.behavior.service.completed_by sR jR tR)
      (I.Prosa_Validation_ServiceInterface_completedByProjection_inst7 LJ dJ PSL sL jcL jL tL).
  Proof.
    intros Hj Ht. unfold prosa.behavior.service.completed_by.
    exact (svc_decide_le_related _ _ _ _ (it_job_cost _ _ Hj) (sc_service_related _ _ _ _ Hj Ht)).
  Qed.

  Lemma sc_has_arrived_related (jR : JR) jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (prosa.behavior.arrival_sequence.has_arrived jR tR)
      (I.Prosa_Behavior_Arrival_sequence_has_arrived_inst1 LJ dJ jaL jL tL).
  Proof.
    intros Hj Ht. unfold prosa.behavior.arrival_sequence.has_arrived.
    exact (svc_decide_le_related _ _ _ _ (it_job_arrival _ _ Hj) Ht).
  Qed.

  Lemma sc_pending_related (jR : JR) jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (prosa.behavior.service.pending sR jR tR)
      (I.Prosa_Behavior_Service_pending_inst7 LJ dJ PSL sL jcL jaL jL tL).
  Proof.
    intros Hj Ht. unfold prosa.behavior.service.pending.
    exact (svc_bool_and_related _ _ _ _ (sc_has_arrived_related _ _ _ _ Hj Ht)
      (svc_bool_not_related _ _ (sc_completed_by_related _ _ _ _ Hj Ht))).
  Qed.
End Sched.

(** ** Job lists *)

Definition JListRel (xsR : seq JR) (xsL : I.List_inst1 LJ) : SProp :=
  ArListRel (map it_job_export xsR) xsL.

Definition sc_jobs_import (xs : I.List_inst1 LJ) : seq JR := map it_job_import (ar_list_to_rocq xs).

Lemma sc_jobs_target_roundtrip xs : JListRel (sc_jobs_import xs) xs.
Proof.
  unfold JListRel, sc_jobs_import. rewrite -map_comp (eq_map sc_job_cancel) map_id.
  exact (ar_list_target_roundtrip xs).
Qed.

Lemma sc_jobs_source_roundtrip xs : Logic.eq (sc_jobs_import (ar_list_to_imported (map it_job_export xs))) xs.
Proof.
  unfold sc_jobs_import. rewrite ar_list_source_roundtrip -map_comp.
  rewrite (eq_map it_job_source_roundtrip). exact (map_id xs).
Qed.

Lemma sc_job_mem (jR : JR) jL xsR xsL :
  ItJobRel jR jL -> JListRel xsR xsL ->
  PropSPropRel (jR \in xsR) (ar_target_mem jL xsL).
Proof.
  intros Hj Hxs. rewrite -(mem_map sc_job_export_inj) (sc_job_rel_eq _ _ Hj).
  exact (ar_membership_correspondence LJ jL _ _ Hxs).
Qed.

Lemma sc_jobs_uniq xsR xsL : JListRel xsR xsL ->
  PropSPropRel (uniq xsR) (I.List_Nodup_inst1 LJ xsL).
Proof.
  intro H. rewrite -(map_inj_uniq sc_job_export_inj).
  exact (ar_uniq_correspondence LJ _ _ H).
Qed.

Definition sc_target_append (a b : I.List_inst1 LJ) : I.List_inst1 LJ :=
  I.HAppend_hAppend_inst7 (I.List_inst1 LJ) (I.List_inst1 LJ) (I.List_inst1 LJ)
    (I.instHAppendOfAppend_inst1 (I.List_inst1 LJ) (I.List_instAppend_inst1 LJ)) a b.

Fixpoint sc_jobs_append (a b : seq JR) :
    Lean.eq (ar_list_to_imported (map it_job_export (a ++ b)))
      (sc_target_append (ar_list_to_imported (map it_job_export a)) (ar_list_to_imported (map it_job_export b))) :=
  match a with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons_inst1 LJ (it_job_export x)) _ _ (sc_jobs_append tail b)
  end.

Definition JFamRel (fR : nat -> seq JR) (fL : Lean.Nat -> I.List_inst1 LJ) : SProp :=
  forall nR nL, SubNatRel nR nL -> JListRel (fR nR) (fL nL).

(** The half-open concatenation (the accepted facts/job_constructor [bigCat] relations, at this export's
    concrete-job [bigCat] equations). *)
Lemma sc_bigcat_delta (fR : nat -> seq JR) (fL : Lean.Nat -> I.List_inst1 LJ) (m d : nat) :
  JFamRel fR fL ->
  JListRel (\cat_(m <= i < m + d) fR i)
    (I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m)
      (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d)) fL).
Proof.
  intro Hf. induction d as [|d IH].
  - rewrite addn0 big_geq //.
    unfold JListRel, ArListRel. cbn.
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_RefSchedInterface_production_bigCat_job_same (sub_nat_to_imported m) fL)).
  - rewrite addnS big_nat_recr; try exact (leq_addr d m).
    have Happ : JListRel (\cat_(m <= i < m + d) fR i ++ fR (m + d))
        (sc_target_append
          (I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m)
            (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d)) fL)
          (fL (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d)))) :=
      sub_imported_eq_trans _ _ _ (sc_jobs_append _ _)
        (sub_imported_eq_congr2 sc_target_append _ _ _ _ IH
          (Hf (m + d) _ (sub_add_correspondence m (sub_nat_to_imported m) d (sub_nat_to_imported d)
            (sub_nat_rel_canonical m) (sub_nat_rel_canonical d)))).
    unfold JListRel, ArListRel in Happ |- *.
    exact (sub_imported_eq_trans _ _ _ Happ
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_RefSchedInterface_production_bigCat_job_add_succ
          (sub_nat_to_imported m) (sub_nat_to_imported d) fL))).
Qed.

Lemma sc_bigcat_canonical (fR : nat -> seq JR) (fL : Lean.Nat -> I.List_inst1 LJ) (m n : nat) :
  JFamRel fR fL ->
  JListRel (\cat_(m <= i < n) fR i)
    (I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m) (sub_nat_to_imported n) fL).
Proof.
  intro Hf. unfold JListRel, ArListRel.
  apply coq_eq_to_imported_eq.
  case Hmn: (m <= n)%N.
  - have Hn : m + (n - m) = n by rewrite addnC subnK.
    rewrite -Hn.
    have HdeltaP := imported_eq_to_coq_eq _ _ (sc_bigcat_delta fR fL m (n - m) Hf).
    etransitivity; first exact HdeltaP.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_congr
      (fun upper => I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m) upper fL) _ _
      (sub_imported_eq_sym _ _
        (sub_add_correspondence m (sub_nat_to_imported m) (n - m) (sub_nat_to_imported (n - m))
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical (n - m))))).
  - have Hlt : (n < m)%N by rewrite ltnNge Hmn.
    have Hnm : (n <= m)%N := ltnW Hlt.
    rewrite big_geq //.
    have HleL := prop_to_sprop _ _
      (sub_nat_le_correspondence n (sub_nat_to_imported n) m (sub_nat_to_imported m)
        (sub_nat_rel_canonical n) (sub_nat_rel_canonical m)) Hnm.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_RefSchedInterface_production_bigCat_job_of_le
        (sub_nat_to_imported m) (sub_nat_to_imported n) fL HleL)).
Qed.

Lemma sc_bigcat_related (fR : nat -> seq JR) (fL : Lean.Nat -> I.List_inst1 LJ) mR mL nR nL :
  JFamRel fR fL -> SubNatRel mR mL -> SubNatRel nR nL ->
  JListRel (\cat_(mR <= i < nR) fR i) (I.Prosa_Util_Notation_bigCat_inst1 LJ mL nL fL).
Proof.
  intros Hf Hm Hn. destruct Hm. destruct Hn. exact (sc_bigcat_canonical fR fL mR nR Hf).
Qed.

(** Filter (the accepted [ar_filter_canonical] proof, with the predicate related through [ItJobRel]). *)
Lemma sc_filter_related (pR : JR -> bool) (pL : LJ -> I.Bool) xsR xsL :
  (forall jR jL, ItJobRel jR jL -> SvcBoolRel (pR jR) (pL jL)) -> JListRel xsR xsL ->
  JListRel [seq x <- xsR | pR x] (I.List_filter_inst1 LJ pL xsL).
Proof.
  intros Hp Hxs. unfold JListRel, ArListRel in *. destruct Hxs.
  induction xsR as [|x xs IH].
  - exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_RefSchedInterface_production_filter_job_nil pL)).
  - refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_RefSchedInterface_production_filter_job_cons pL (it_job_export x)
        (ar_list_to_imported (map it_job_export xs))))).
    have Hx := Hp x (it_job_export x) (@Lean.eq_refl _ _). unfold SvcBoolRel in Hx.
    revert Hx. generalize (pL (it_job_export x)). intros b Hx. destruct Hx.
    cbn. destruct (pR x); cbn.
    + exact (sub_imported_eq_congr (I.List_cons_inst1 LJ (it_job_export x)) _ _ IH).
    + exact IH.
Qed.

(** ** Arrival sequences *)

Notation ArrR := (prosa.behavior.arrival_sequence.arrival_sequence T.concrete_job).
Notation ArrL := (I.Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1 LJ dJ).

Definition JArrRel (arrR : ArrR) (arrL : ArrL) : SProp := JFamRel arrR arrL.

Definition sc_arr_export (arrR : ArrR) : ArrL :=
  fun tL => ar_list_to_imported (map it_job_export (arrR (sub_nat_to_rocq tL))).

Definition sc_arr_import (arrL : ArrL) : ArrR :=
  fun tR => sc_jobs_import (arrL (sub_nat_to_imported tR)).

Lemma sc_arr_export_rel arrR : JArrRel arrR (sc_arr_export arrR).
Proof.
  intros tR tL Ht. unfold JListRel, ArListRel, sc_arr_export.
  rewrite (sc_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
Qed.

Lemma sc_arr_import_rel arrL : JArrRel (sc_arr_import arrL) arrL.
Proof.
  intros tR tL Ht. unfold sc_arr_import.
  exact (sc_lean_transport (fun y => JListRel (sc_jobs_import (arrL (sub_nat_to_imported tR))) (arrL y)) _ _ Ht
    (sc_jobs_target_roundtrip _)).
Qed.

Lemma sc_forall_arr (PR : ArrR -> Prop) (PL : ArrL -> SProp) :
  (forall aR aL, JArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) ->
  PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (sc_forall_cover JArrRel sc_arr_export sc_arr_import PR PL sc_arr_export_rel sc_arr_import_rel). Qed.

Section Arrivals.
  Variable arrR : ArrR.
  Variable arrL : ArrL.
  Hypothesis Harr : JArrRel arrR arrL.

  Lemma sc_arrivals_between_related t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    JListRel (prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R)
      (I.Prosa_Behavior_Arrival_sequence_arrivals_between_inst1 LJ dJ arrL t1L t2L).
  Proof.
    intros H1 H2. unfold prosa.behavior.arrival_sequence.arrivals_between.
    cbn [I.Prosa_Behavior_Arrival_sequence_arrivals_between_inst1].
    exact (sc_bigcat_related _ _ _ _ _ _ Harr H1 H2).
  Qed.

  Lemma sc_arrivals_up_to_related tR tL :
    SubNatRel tR tL ->
    JListRel (prosa.behavior.arrival_sequence.arrivals_up_to arrR tR)
      (I.Prosa_Behavior_Arrival_sequence_arrivals_up_to_inst1 LJ dJ arrL tL).
  Proof.
    intro Ht. unfold prosa.behavior.arrival_sequence.arrivals_up_to.
    cbn [I.Prosa_Behavior_Arrival_sequence_arrivals_up_to_inst1].
    exact (sc_arrivals_between_related _ _ _ _ (sub_nat_rel_canonical O)
      (sc_src_transport (fun x => SubNatRel x _) _ _ (addn1 tR)
        (sub_add_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 1)))).
  Qed.

  Lemma sc_arrives_at_related (jR : JR) jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (prosa.behavior.arrival_sequence.arrives_at arrR jR tR)
      (I.Prosa_Behavior_Arrival_sequence_arrives_at_inst1 LJ dJ arrL jL tL).
  Proof.
    intros Hj Ht. unfold prosa.behavior.arrival_sequence.arrives_at.
    cbn [I.Prosa_Behavior_Arrival_sequence_arrives_at_inst1].
    apply svc_decide_bool_correspondence.
    exact (sc_job_mem _ _ _ _ Hj (Harr _ _ Ht)).
  Qed.

  Lemma sc_arrives_in_related (jR : JR) jL :
    ItJobRel jR jL ->
    PropSPropRel (prosa.behavior.arrival_sequence.arrives_in arrR jR)
      (I.Prosa_Behavior_Arrival_sequence_arrives_in_inst1 LJ dJ arrL jL).
  Proof.
    intro Hj. unfold prosa.behavior.arrival_sequence.arrives_in.
    cbn [I.Prosa_Behavior_Arrival_sequence_arrives_in_inst1].
    apply sc_exists_nat. intros tR tL Ht.
    exact (svc_bool_truth_correspondence _ _ (sc_arrives_at_related _ _ _ _ Hj Ht)).
  Qed.

  Lemma sc_valid_arrival_sequence_related :
    PropSPropRel (prosa.behavior.arrival_sequence.valid_arrival_sequence arrR)
      (I.Prosa_Behavior_Arrival_sequence_valid_arrival_sequence_inst1 LJ dJ jaL arrL).
  Proof.
    unfold prosa.behavior.arrival_sequence.valid_arrival_sequence.
    cbn [I.Prosa_Behavior_Arrival_sequence_valid_arrival_sequence_inst1].
    apply sc_and.
    - unfold prosa.behavior.arrival_sequence.consistent_arrival_times.
      cbn [I.Prosa_Behavior_Arrival_sequence_consistent_arrival_times_inst1].
      apply sc_forall_job. intros jR jL Hj.
      apply sc_forall_nat. intros tR tL Ht.
      apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_arrives_at_related _ _ _ _ Hj Ht)).
      exact (sub_nat_eq_correspondence _ _ _ _ (it_job_arrival _ _ Hj) Ht).
    - unfold prosa.behavior.arrival_sequence.arrival_sequence_uniq.
      cbn [I.Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq_inst1].
      apply sc_forall_nat. intros tR tL Ht.
      exact (sc_jobs_uniq _ _ (Harr _ _ Ht)).
  Qed.
End Arrivals.

(** ** The ideal-uniprocessor scheduler *)

Notation RMR := (@prosa.behavior.ready.JobReady T.concrete_job PSR T.JobCost T.JobArrival).
Notation RML := (I.Prosa_Behavior_Ready_JobReady_inst7 LJ dJ PSL jcL jaL).
Notation JPR := (prosa.model.preemption.parameter.JobPreemptable T.concrete_job).
Notation JPL := (I.Prosa_Model_Preemption_Parameter_JobPreemptable_inst1 LJ dJ).
Notation HPR := (prosa.model.priority.definitions.JLDP_policy T.concrete_job).
Notation HPL := (I.Prosa_Model_Priority_Definitions_JLDP_policy_inst1 LJ dJ).

Definition ScReadyRel (rmR : RMR) (rmL : RML) : SProp :=
  forall sR sL, JSchedRel sR sL -> forall jR jL tR tL, ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.ready.job_ready JR PSR T.JobCost T.JobArrival rmR sR jR tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready_inst7 LJ dJ PSL jcL jaL rmL sL jL tL).

Definition ScPreemptRel (jpR : JPR) (jpL : JPL) : SProp :=
  forall jR jL nR nL, ItJobRel jR jL -> SubNatRel nR nL ->
    SvcBoolRel (@prosa.model.preemption.parameter.job_preemptable JR jpR jR nR)
      (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable_inst1 LJ dJ jpL jL nL).

Definition ScPolicyRel (hpR : HPR) (hpL : HPL) : SProp :=
  forall tR tL, SubNatRel tR tL -> forall xR xL yR yL, ItJobRel xR xL -> ItJobRel yR yL ->
    SvcBoolRel (@prosa.model.priority.definitions.hep_job_at JR hpR tR xR yR)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at_inst1 LJ dJ hpL tL xL yL).

Lemma sc_nat_not_eq (tR t'R : nat) (tL t'L : Lean.Nat) :
  SubNatRel tR tL -> SubNatRel t'R t'L -> t'R <> tR -> I.Not (Lean.eq tL t'L).
Proof.
  intros Ht Ht' NE. unfold I.Not. intro EL.
  refine (match NE _ return I.False with end).
  rewrite -(sc_nat_input _ _ Ht) -(sc_nat_input _ _ Ht').
  exact (Logic.eq_sym (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))).
Qed.

Lemma sc_succ_related (tR : nat) (tL : Lean.Nat) :
  SubNatRel tR tL ->
  SubNatRel tR.+1 (I.HAdd_hAdd_inst7 Lean.Nat I.Prosa_Behavior_Time_instant Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) tL
    (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_instant 1 (I.instOfNatNat 1))).
Proof.
  intro Ht.
  exact (sc_src_transport (fun x => SubNatRel x _) _ _ (addn1 tR)
    (sub_add_correspondence _ _ _ _ Ht (@Lean.eq_refl _ _))).
Qed.

(** *** The generic scheduler at the ideal processor *)

Section Generic.
  Variable polR : SchedR -> nat -> option JR.
  Variable polL : I.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy_inst7 LJ dJ PSL.
  Hypothesis Hpol : forall sR sL, JSchedRel sR sL -> forall tR tL, SubNatRel tR tL ->
    JOptRel (polR sR tR) (polL sL tL).

  Let emptyR := @prosa.implementation.definitions.generic_scheduler.empty_schedule JR PSR None.
  Let emptyL := I.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule_inst7 LJ dJ PSL
    (I.Option_none_inst1 LJ).
  Let sutR h := @prosa.implementation.definitions.generic_scheduler.schedule_up_to JR PSR polR None h.
  Let sutL h := I.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst7 LJ dJ PSL polL
    (I.Option_none_inst1 LJ) h.

  Lemma sc_empty_related : JSchedRel emptyR emptyL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_RefSchedInterface_production_empty_schedule_job (I.Option_none_inst1 LJ) tL)).
  Qed.

  Lemma sc_replace_at_related (sR : SchedR) (sL : SchedL) (t'R : nat) (t'L : Lean.Nat)
      (nsR : option JR) (nsL : StL) :
    JSchedRel sR sL -> SubNatRel t'R t'L -> JOptRel nsR nsL ->
    JSchedRel (@prosa.analysis.transform.swap.replace_at JR PSR sR t'R nsR)
      (I.Prosa_Analysis_Transform_Swap_replace_at_inst7 LJ dJ PSL sL t'L nsL).
  Proof.
    intros Hs Ht' Hns tR tL Ht.
    destruct (@eqP nat t'R tR) as [E|NE].
    - refine (sc_src_transport (fun o => JOptRel o _) nsR _ _ _).
      + subst tR. rewrite /prosa.analysis.transform.swap.replace_at eqxx; reflexivity.
      + subst tR.
        exact (sub_imported_eq_trans _ _ _ Hns (sub_imported_eq_sym _ _
          (I.Prosa_Validation_RefSchedInterface_production_replace_at_job_same sL t'L nsL tL
            (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ht) Ht')))).
    - refine (sc_src_transport (fun o => JOptRel o _) (sR tR) _ _ _).
      + move/eqP: NE => NE. rewrite /prosa.analysis.transform.swap.replace_at (negbTE NE); reflexivity.
      + exact (sub_imported_eq_trans _ _ _ (Hs tR tL Ht) (sub_imported_eq_sym _ _
          (I.Prosa_Validation_RefSchedInterface_production_replace_at_job_other sL t'L nsL tL
            (sc_nat_not_eq _ _ _ _ Ht Ht' NE)))).
  Qed.

  Lemma sc_sut_canonical (hR : nat) : JSchedRel (sutR hR) (sutL (sub_nat_to_imported hR)).
  Proof.
    induction hR as [|h IH].
    - have H0 := sub_nat_rel_canonical O.
      exact (sc_lean_transport (fun y => JSchedRel (sutR O) y) _ _
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_RefSchedInterface_production_schedule_up_to_job_zero polL (I.Option_none_inst1 LJ)))
        (sc_replace_at_related _ _ _ _ _ _ sc_empty_related H0 (Hpol _ _ sc_empty_related _ _ H0))).
    - have Hh := sub_nat_rel_canonical h.
      have Hh1 := sc_succ_related _ _ Hh.
      refine (sc_lean_transport (fun y => JSchedRel (sutR h.+1) (sutL y)) _ _
        (sub_imported_eq_sym _ _ Hh1) _).
      exact (sc_lean_transport (fun y => JSchedRel (sutR h.+1) y) _ _
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_RefSchedInterface_production_schedule_up_to_job_succ polL (I.Option_none_inst1 LJ)
            (sub_nat_to_imported h)))
        (sc_replace_at_related _ _ _ _ _ _ IH Hh1 (Hpol _ _ IH _ _ Hh1))).
  Qed.

  Lemma sc_sut_related (hR : nat) (hL : Lean.Nat) : SubNatRel hR hL -> JSchedRel (sutR hR) (sutL hL).
  Proof. intro Hh. exact (sc_lean_transport (fun y => JSchedRel (sutR hR) (sutL y)) _ _ Hh (sc_sut_canonical hR)). Qed.

  Lemma sc_generic_schedule_related :
    JSchedRel (@prosa.implementation.definitions.generic_scheduler.generic_schedule JR PSR polR None)
      (I.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule_inst7 LJ dJ PSL polL
        (I.Option_none_inst1 LJ)).
  Proof.
    intros tR tL Ht.
    exact (sc_sut_related tR tL Ht tR tL Ht).
  Qed.
End Generic.

(** *** Supremum *)

Lemma sc_choose_superior_related (R : JR -> JR -> bool) (RL : LJ -> LJ -> I.Bool)
    (HR : forall xR xL yR yL, ItJobRel xR xL -> ItJobRel yR yL -> SvcBoolRel (R xR yR) (RL xL yL))
    (xR : JR) xL oR oL :
  ItJobRel xR xL -> JOptRel oR oL ->
  JOptRel (@prosa.util.supremum.choose_superior JR R xR oR) (I.Prosa_Util_Supremum_choose_superior_inst1 LJ RL xL oL).
Proof.
  intros Hx Ho. destruct Hx. destruct Ho.
  destruct oR as [y|].
  - have Hb := HR xR _ y _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _).
    unfold prosa.util.supremum.choose_superior.
    refine (sc_lean_transport (fun b => JOptRel (if R xR y then Some xR else Some y)
      (I.ite (I.Option_inst1 LJ) (Lean.eq b I.Bool_true) (I.instDecidableEqBool b I.Bool_true)
        (I.Option_some_inst1 LJ (it_job_export xR)) (I.Option_some_inst1 LJ (it_job_export y)))) _ _ Hb _).
    destruct (R xR y); exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma sc_supremum_related (R : JR -> JR -> bool) (RL : LJ -> LJ -> I.Bool)
    (HR : forall xR xL yR yL, ItJobRel xR xL -> ItJobRel yR yL -> SvcBoolRel (R xR yR) (RL xL yL))
    xsR xsL :
  JListRel xsR xsL ->
  JOptRel (@prosa.util.supremum.supremum JR R xsR) (I.Prosa_Util_Supremum_supremum_inst1 LJ RL xsL).
Proof.
  intro Hxs. unfold JListRel, ArListRel in Hxs. destruct Hxs.
  induction xsR as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sc_choose_superior_related R RL HR x _ _ _ (@Lean.eq_refl _ _) IH).
Qed.

Theorem sc_choose_highest_prio_job_related (hpR : HPR) (hpL : HPL) (Hhp : ScPolicyRel hpR hpL) tR tL xsR xsL :
  SubNatRel tR tL -> JListRel xsR xsL ->
  JOptRel (@prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job JR hpR tR xsR)
    (I.Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job_inst1 LJ dJ hpL tL xsL).
Proof.
  intros Ht Hxs. exact (sc_supremum_related _ _ (Hhp tR tL Ht) _ _ Hxs).
Qed.

Section Scheduler.
  Variable rmR : RMR.
  Variable rmL : RML.
  Hypothesis Hrm : ScReadyRel rmR rmL.
  Variable jpR : JPR.
  Variable jpL : JPL.
  Hypothesis Hjp : ScPreemptRel jpR jpL.
  Variable arrR : ArrR.
  Variable arrL : ArrL.
  Hypothesis Harr : JArrRel arrR arrL.

  Let ONE := sub_nat_rel_canonical (S O).

  Lemma sc_prev_inner (o : option JR) oL (bR : JR -> bool) (bL : LJ -> I.Bool) :
    JOptRel o oL -> (forall jR jL, ItJobRel jR jL -> SvcBoolRel (bR jR) (bL jL)) ->
    SvcBoolRel (if o is Some j then bR j else false)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_match_1_inst1 LJ dJ
        (fun _ : StL => I.Bool) oL bL (fun _ : I.Unit => I.Bool_false)).
  Proof.
    intros Ho Hb. destruct Ho. destruct o as [j|].
    - exact (Hb j _ (@Lean.eq_refl _ _)).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Theorem sc_prev_job_nonpreemptive_related (sR : SchedR) (sL : SchedL) tR tL :
    JSchedRel sR sL -> SubNatRel tR tL ->
    SvcBoolRel (@prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive JR T.JobCost
        T.JobArrival rmR jpR sR tR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_inst1 LJ dJ jcL jaL rmL jpL sL tL).
  Proof.
    intros Hs Ht.
    refine (sc_lean_transport (fun y => SvcBoolRel
      (@prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive JR T.JobCost T.JobArrival
        rmR jpR sR tR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_inst1 LJ dJ jcL jaL rmL jpL sL y))
      _ _ Ht _).
    destruct tR as [|t].
    - exact (@Lean.eq_refl _ _).
    - have Ht1 := sub_nat_rel_canonical t.+1.
      exact (sc_prev_inner (sR t) (sL (sub_nat_to_imported t)) _ _ (Hs _ _ (sub_nat_rel_canonical t))
        (fun jR jL Hj => svc_bool_and_related _ _ _ _ (Hrm _ _ Hs _ _ _ _ Hj Ht1)
          (svc_bool_not_related _ _ (Hjp _ _ _ _ Hj (sc_service_related _ _ Hs _ _ _ _ Hj Ht1))))).
  Qed.

  Lemma sc_backlogged_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) jR jL tR tL :
    ItJobRel jR jL -> SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.ready.backlogged JR PSR T.JobCost T.JobArrival rmR sR jR tR)
      (I.Prosa_Behavior_Ready_backlogged_inst7 LJ dJ PSL jcL jaL rmL sL jL tL).
  Proof.
    intros Hj Ht. unfold prosa.behavior.ready.backlogged.
    exact (svc_bool_and_related _ _ _ _ (Hrm _ _ Hs _ _ _ _ Hj Ht)
      (svc_bool_not_related _ _ (sc_scheduled_at_related _ _ Hs _ _ _ _ Hj Ht))).
  Qed.

  Lemma sc_jobs_backlogged_at_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) tR tL :
    SubNatRel tR tL ->
    JListRel (@prosa.model.schedule.work_conserving.jobs_backlogged_at JR T.JobArrival T.JobCost PSR rmR arrR sR tR)
      (I.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst7 LJ dJ jaL jcL PSL rmL arrL sL tL).
  Proof.
    intro Ht.
    exact (sc_filter_related _ _ _ _ (fun jR jL Hj => sc_backlogged_related _ _ Hs _ _ _ _ Hj Ht)
      (sc_arrivals_up_to_related _ _ Harr _ _ Ht)).
  Qed.

  Lemma sc_cond_related (b : bool) xR yR xL yL :
    JOptRel xR xL -> JOptRel yR yL ->
    JOptRel (if b then xR else yR) (I.cond (I.Option_inst1 LJ) (svc_bool_to_imported b) xL yL).
  Proof. intros Hx Hy. destruct b; [exact Hx | exact Hy]. Qed.

  Section Alloc.
    Variable cjR : nat -> seq JR -> option JR.
    Variable cjL : I.Prosa_Behavior_Time_instant -> I.List_inst1 LJ -> I.Option_inst1 LJ.
    Hypothesis Hcj : forall tR tL, SubNatRel tR tL -> forall xsR xsL, JListRel xsR xsL ->
      JOptRel (cjR tR xsR) (cjL tL xsL).

    Theorem sc_allocation_at_related (sR : SchedR) (sL : SchedL) tR tL :
      JSchedRel sR sL -> SubNatRel tR tL ->
      JOptRel (@prosa.implementation.definitions.ideal_uni_scheduler.allocation_at JR T.JobCost T.JobArrival
          arrR rmR jpR cjR sR tR)
        (I.Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at_inst1 LJ dJ jcL jaL arrL rmL jpL cjL sL tL).
    Proof.
      intros Hs Ht.
      have Hprev := sc_prev_job_nonpreemptive_related _ _ _ _ Hs Ht.
      have Hpred : SubNatRel tR.-1 (I.HSub_hSub_inst7 I.Prosa_Behavior_Time_instant I.Prosa_Behavior_Time_instant
          I.Prosa_Behavior_Time_instant (I.instHSub_inst1 I.Prosa_Behavior_Time_instant I.instSubNat) tL
          (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_instant 1 (I.instOfNatNat 1))) :=
        sc_src_transport (fun x => SubNatRel x _) _ _ (subn1 tR)
          (svc_target_sub_related _ _ _ _ Ht ONE).
      unfold prosa.implementation.definitions.ideal_uni_scheduler.allocation_at.
      cbn [I.Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at_inst1].
      refine (sc_lean_transport (fun y => JOptRel
        (if @prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive JR T.JobCost T.JobArrival
            rmR jpR sR tR then sR tR.-1
         else cjR tR (@prosa.model.schedule.work_conserving.jobs_backlogged_at JR T.JobArrival T.JobCost PSR rmR
           arrR sR tR))
        (I.cond (I.Option_inst1 LJ) y (sL _) (cjL tL
          (I.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst7 LJ dJ jaL jcL PSL rmL arrL sL tL))))
        _ _ Hprev _).
      exact (sc_cond_related _ _ _ _ _ (Hs _ _ Hpred)
        (Hcj _ _ Ht _ _ (sc_jobs_backlogged_at_related _ _ Hs _ _ Ht))).
    Qed.

    Theorem sc_pmc_uni_schedule_related :
      JSchedRel (@prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule JR T.JobCost T.JobArrival
          arrR rmR jpR cjR)
        (I.Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule_inst1 LJ dJ jcL jaL arrL rmL jpL cjL).
    Proof.
      exact (sc_generic_schedule_related _ _
        (fun sR sL Hs tR tL Ht => sc_allocation_at_related sR sL tR tL Hs Ht)).
    Qed.
  End Alloc.

  Theorem sc_uni_schedule_related (hpR : HPR) (hpL : HPL) (Hhp : ScPolicyRel hpR hpL) :
    JSchedRel (@prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule JR T.JobCost T.JobArrival
        arrR rmR jpR hpR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule_inst1 LJ dJ jcL jaL arrL rmL jpL hpL).
  Proof.
    exact (sc_pmc_uni_schedule_related _ _
      (fun tR tL Ht xsR xsL Hxs => sc_choose_highest_prio_job_related hpR hpL Hhp tR tL xsR xsL Ht Hxs)).
  Qed.

  (** *** Schedule properties *)

  Lemma sc_preemption_time_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) tR tL :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.model.schedule.preemption_time.preemption_time JR jpR arrR PSR sR tR)
      (I.Prosa_Model_Schedule_PreemptionTime_preemption_time_inst7 LJ dJ jpL arrL PSL sL tL).
  Proof.
    intro Ht.
    have Hl : JListRel (prosa.model.schedule.scheduled.scheduled_jobs_at arrR sR tR)
        (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at_inst7 LJ dJ PSL arrL sL tL) :=
      sc_filter_related (fun j => prosa.behavior.service.scheduled_at sR j tR)
        (fun j => I.Prosa_Behavior_Service_scheduled_at_inst7 LJ dJ PSL sL j tL) _ _
        (fun jR jL Hj => sc_scheduled_at_related _ _ Hs _ _ _ _ Hj Ht)
        (sc_arrivals_up_to_related _ _ Harr _ _ Ht).
    assert (Hsj : JOptRel (prosa.model.schedule.scheduled.scheduled_job_at arrR sR tR)
        (I.Prosa_Model_Schedule_Scheduled_scheduled_job_at_inst7 LJ dJ PSL arrL sL tL)).
    { unfold prosa.model.schedule.scheduled.scheduled_job_at.
      cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_job_at_inst7].
      unfold JListRel, ArListRel in Hl.
      refine (sc_lean_transport (fun y => JOptRel (ohead (prosa.model.schedule.scheduled.scheduled_jobs_at arrR sR tR))
        (I.List_head__q_inst1 LJ y)) _ _ Hl _).
      destruct (prosa.model.schedule.scheduled.scheduled_jobs_at arrR sR tR); exact (@Lean.eq_refl _ _). }
    unfold prosa.model.schedule.preemption_time.preemption_time.
    cbn [I.Prosa_Model_Schedule_PreemptionTime_preemption_time_inst7].
    refine (sc_lean_transport (fun y => SvcBoolRel
      (if prosa.model.schedule.scheduled.scheduled_job_at arrR sR tR is Some j then
         @prosa.model.preemption.parameter.job_preemptable JR jpR j (prosa.behavior.service.service sR j tR)
       else true)
      (I.Prosa_Model_Schedule_PreemptionTime_preemption_time_match_1_inst1 LJ (fun _ => I.Bool) y
        (fun j => I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable_inst1 LJ dJ jpL j
          (I.Prosa_Behavior_Service_service_inst7 LJ dJ PSL sL j tL))
        (fun _ => I.Bool_true))) _ _ Hsj _).
    destruct (prosa.model.schedule.scheduled.scheduled_job_at arrR sR tR) as [j|].
    - exact (Hjp _ _ _ _ (@Lean.eq_refl _ _) (sc_service_related _ _ Hs _ _ _ _ (@Lean.eq_refl _ _) Ht)).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Lemma sc_jobs_come_from_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) :
    PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
      (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst7 LJ dJ PSL sL arrL).
  Proof.
    unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
    cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst7].
    apply sc_forall_job. intros jR jL Hj.
    apply sc_forall_nat. intros tR tL Ht.
    apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_scheduled_at_related _ _ Hs _ _ _ _ Hj Ht)).
    exact (sc_arrives_in_related _ _ Harr _ _ Hj).
  Qed.

  Lemma sc_must_be_ready_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) :
    PropSPropRel (@prosa.behavior.ready.jobs_must_be_ready_to_execute JR T.JobArrival PSR sR T.JobCost rmR)
      (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst7 LJ dJ jaL PSL sL jcL rmL).
  Proof.
    unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
    cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst7].
    apply sc_forall_job. intros jR jL Hj.
    apply sc_forall_nat. intros tR tL Ht.
    apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_scheduled_at_related _ _ Hs _ _ _ _ Hj Ht)).
    exact (svc_bool_truth_correspondence _ _ (Hrm _ _ Hs _ _ _ _ Hj Ht)).
  Qed.

  Lemma sc_valid_schedule_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL) :
    PropSPropRel (@prosa.behavior.ready.valid_schedule JR T.JobArrival PSR sR T.JobCost rmR arrR)
      (I.Prosa_Behavior_Ready_valid_schedule_inst7 LJ dJ jaL PSL sL jcL rmL arrL).
  Proof.
    unfold prosa.behavior.ready.valid_schedule.
    cbn [I.Prosa_Behavior_Ready_valid_schedule_inst7].
    exact (sc_and (sc_jobs_come_from_related _ _ Hs) (sc_must_be_ready_related _ _ Hs)).
  Qed.

  Lemma sc_respects_JLDP_related (sR : SchedR) (sL : SchedL) (Hs : JSchedRel sR sL)
      (hpR : HPR) (hpL : HPL) (Hhp : ScPolicyRel hpR hpL) :
    PropSPropRel (@prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point JR T.JobArrival
        T.JobCost PSR jpR rmR arrR sR hpR)
      (I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point_inst7 LJ dJ jaL jcL PSL
        jpL rmL arrL sL hpL).
  Proof.
    unfold prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point.
    cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point_inst7].
    apply sc_forall_job. intros jR jL Hj.
    apply sc_forall_job. intros hR hL Hh.
    apply sc_forall_nat. intros tR tL Ht.
    apply sc_imp; first exact (sc_arrives_in_related _ _ Harr _ _ Hj).
    apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_preemption_time_related _ _ Hs _ _ Ht)).
    apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_backlogged_related _ _ Hs _ _ _ _ Hj Ht)).
    apply sc_imp; first exact (svc_bool_truth_correspondence _ _ (sc_scheduled_at_related _ _ Hs _ _ _ _ Hh Ht)).
    exact (svc_bool_truth_correspondence _ _ (Hhp _ _ Ht _ _ _ _ Hh Hj)).
  Qed.
End Scheduler.
