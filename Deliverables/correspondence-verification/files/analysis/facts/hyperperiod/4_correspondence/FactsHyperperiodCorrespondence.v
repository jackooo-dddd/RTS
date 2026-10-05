From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From prosa Require Import FactsHyperperiodSemanticSource.
From prosa Require Import model.task.arrivals analysis.definitions.infinite_jobs.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsHyperperiod ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskOffsetCorrespondence PeriodicCorrespondence
  NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence
  HyperperiodCorrespondence InfiniteJobsCorrespondence.

Module I := ImportedFactsHyperperiod.
Module S := FactsHyperperiodSemanticSource.FactsHyperperiodSemanticSource.
Module O := TaskOffsetSemanticSource.TaskOffsetSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Statement correspondences for [analysis/facts/hyperperiod.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the task offsets where they
    occur, the periodic model, [job_task], [job_arrival] and the arrival
    sequence); target side: the imported Lean theorem types at related inputs
    (the accepted [OffRel] and [PerRel], [Lean.eq] on [job_task],
    [ArJobArrivalRel], [ArArrivalSequenceRel]).  Tasks and jobs are identity
    carriers, Nats are covered in both directions, task sets (quantified
    inside the statements) are covered in both directions by the accepted
    canonical list conversion and its round trips.  The hyperperiod
    definitions go through the accepted [HyperperiodCorrespondence], the
    arithmetic through the accepted Nat addition, multiplication, subtraction
    and division relations, list membership and sizes through the accepted
    arrivals certificates, and validity, offsets, periods, the periodic task
    model and [infinite_jobs] through the accepted certificates
    re-instantiated at this artifact.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** Task sets quantified inside a statement: both directions via the
    canonical list conversions. *)
Lemma fhyp_forall_list_correspondence (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR xsL.
    exact (prop_to_sprop _ _ (HP (ar_list_to_rocq xsL) xsL (ar_list_target_roundtrip xsL))
      (HR (ar_list_to_rocq xsL))).
  - intro HL. apply strictly_inhabits. intro xsR.
    exact (sprop_to_prop _ _ (HP xsR (ar_list_to_imported xsR) (@Lean.eq_refl _ _))
      (HL (ar_list_to_imported xsR))).
Qed.

(** Equality over an identity carrier, both sides mapped by related maps. *)
Lemma fhyp_eq_identity_correspondence (T : Type) (aR aL bR bL : T) :
  Lean.eq aR aL -> Lean.eq bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ha) Hb).
  - intro E. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Ha (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hb)))).
Qed.

Section Hyperperiod.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable pR : P.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel Task pR pL.

  Let HYP tsR tsL (Hts : ArListRel tsR tsL) :=
    hyperperiod_correspondence Task pR pL Hp tsR tsL Hts.
  Let MEM tsk tsR tsL (Hts : ArListRel tsR tsL) :=
    ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk tsR tsL Hts).

  Definition src_hyperperiod_int_mult_of_any_task : Prop :=
    ltac:(body_of (fun s : S.statement_hyperperiod_int_mult_of_any_task => s Task pR)).
  Definition tgt_hyperperiod_int_mult_of_any_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_hyperperiod_int_mult_of_any_task Task dT pL)).
  Theorem hyperperiod_int_mult_of_any_task_correspondence :
    PropSPropRel src_hyperperiod_int_mult_of_any_task tgt_hyperperiod_int_mult_of_any_task.
  Proof.
    apply fhyp_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (MEM tsk _ _ Hts)|].
    apply ar_exists_nat_correspondence. intros kR kL Hk.
    exact (sub_nat_eq_correspondence _ _ _ _ (HYP _ _ Hts) (sub_mul_correspondence _ _ _ _ Hk (Hp tsk))).
  Qed.

  Definition src_valid_periods_imply_pos_hp : Prop :=
    ltac:(body_of (fun s : S.statement_valid_periods_imply_pos_hp => s Task pR)).
  Definition tgt_valid_periods_imply_pos_hp : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_valid_periods_imply_pos_hp Task dT pL)).
  Theorem valid_periods_imply_pos_hp_correspondence :
    PropSPropRel src_valid_periods_imply_pos_hp tgt_valid_periods_imply_pos_hp.
  Proof.
    apply fhyp_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_periods_correspondence Task pR pL Hp tsR tsL Hts)|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (HYP _ _ Hts)).
  Qed.

  Variable oR : O.TaskOffset Task.
  Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
  Hypothesis Hoff : OffRel Task oR oL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let VP tsk := ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk).
  Let RP tsk := respects_periodic_task_model_correspondence Task pR pL Hp Job jtR jtL Hjt jaR jaL Hja
    arrR arrL Harr tsk.
  Let VO tsk := valid_offset_correspondence Task oR oL Hoff Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsk.
  Let INF := infinite_jobs_correspondence Task Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr.
  Let MAX tsR tsL (Hts : ArListRel tsR tsL) := max_task_offset_correspondence Task oR oL Hoff tsR tsL Hts.
  Let JIH tsR tsL (Hts : ArListRel tsR tsL) hR hL (Hh : SubNatRel hR hL) tsk :=
    jobs_in_hyperperiod_correspondence Task Job pR pL Hp jtR jtL Hjt arrR arrL Harr tsR tsL Hts hR hL tsk Hh.
  Let JMEM (j : Job) xsR xsL (Hxs : ArListRel xsR xsL) :=
    ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j xsR xsL Hxs).
  Let ARR (j : Job) := arrives_in_correspondence_certificate Job arrR arrL j Harr.
  Let TSK (j : Job) tsk := fhyp_eq_identity_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ tsk).
  Let LEO tsR tsL (Hts : ArListRel tsR tsL) (j : Job) :=
    sub_nat_le_correspondence _ _ _ _ (MAX tsR tsL Hts) (Hja j).
  (** [n * HP + O_max] and [(job_arrival j - O_max) %/ HP * HP + O_max]. *)
  Let START tsR tsL (Hts : ArListRel tsR tsL) nR nL (Hn : SubNatRel nR nL) :=
    sub_add_correspondence _ _ _ _ (lcmseqdm_mul_correspondence _ _ _ _ Hn (HYP _ _ Hts)) (MAX _ _ Hts).
  Let HPIDX tsR tsL (Hts : ArListRel tsR tsL) (j : Job) :=
    lcmseqdm_div_correspondence _ _ _ _ (ari_nat_sub_related _ _ _ _ (Hja j) (MAX _ _ Hts)) (HYP _ _ Hts).

  Definition src_corresponding_jobs_have_same_task : Prop :=
    ltac:(body_of (fun s : S.statement_corresponding_jobs_have_same_task => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_corresponding_jobs_have_same_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_corresponding_jobs_have_same_task
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem corresponding_jobs_have_same_task_correspondence :
    PropSPropRel src_corresponding_jobs_have_same_task tgt_corresponding_jobs_have_same_task.
  Proof.
    apply fhyp_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    have Hcorr := corresponding_job_in_hyperperiod_correspondence Task Job oR oL Hoff pR pL Hp jtR jtL Hjt
      jaR jaL Hja arrR arrL Harr tsR tsL Hts j1 _ _ (@prosa.model.task.concept.job_task Job Task jtR j1)
      (starting_instant_of_corresponding_hyperperiod_correspondence Task Job oR oL Hoff pR pL Hp jaR jaL Hja
        tsR tsL Hts j2).
    have E := imported_eq_to_coq_eq _ _ (Hjt j1).
    rewrite -E.
    apply fhyp_eq_identity_correspondence.
    - rewrite (imported_eq_to_coq_eq _ _ Hcorr). exact (Hjt _).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Definition src_all_jobs_arrive_within_hyperperiod : Prop :=
    ltac:(body_of (fun s : S.statement_all_jobs_arrive_within_hyperperiod => s Task pR Job jtR jaR arrR)).
  Definition tgt_all_jobs_arrive_within_hyperperiod : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_all_jobs_arrive_within_hyperperiod
      Task dT pL Job dJ jtL jaL arrL)).
  Theorem all_jobs_arrive_within_hyperperiod_correspondence :
    PropSPropRel src_all_jobs_arrive_within_hyperperiod tgt_all_jobs_arrive_within_hyperperiod.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply fhyp_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (JMEM j _ _ (JIH _ _ Hts _ _ Ht tsk))|].
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Ht (Hja j))
      (ar_decide_lt_related _ _ _ _ (Hja j) (sub_add_correspondence _ _ _ _ Ht (HYP _ _ Hts))))).
  Qed.

  Ltac fhyp_size_prefix Hts tsk :=
    apply ar_imp_correspondence; [exact VALID|];
    apply fhyp_forall_list_correspondence; intros ? ? Hts;
    apply ar_forall_identity_correspondence; intro tsk;
    apply ar_imp_correspondence; [exact (MEM tsk _ _ Hts)|];
    apply ar_imp_correspondence; [exact (VO tsk)|];
    apply ar_imp_correspondence; [exact (VP tsk)|];
    apply ar_imp_correspondence; [exact (RP tsk)|];
    apply ar_imp_correspondence; [exact INF|].

  Definition src_eq_size_hyp_lt : Prop :=
    ltac:(body_of (fun s : S.statement_eq_size_hyp_lt => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_eq_size_hyp_lt : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_eq_size_hyp_lt Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem eq_size_hyp_lt_correspondence : PropSPropRel src_eq_size_hyp_lt tgt_eq_size_hyp_lt.
  Proof.
    fhyp_size_prefix Hts tsk.
    apply ar_forall_nat_correspondence. intros n1R n1L Hn1.
    apply ar_forall_nat_correspondence. intros n2R n2L Hn2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hn1 Hn2)|].
    exact (sub_nat_eq_correspondence _ _ _ _
      (ari_size_related Job _ _ (JIH _ _ Hts _ _ (START _ _ Hts _ _ Hn1) tsk))
      (ari_size_related Job _ _ (JIH _ _ Hts _ _ (START _ _ Hts _ _ Hn2) tsk))).
  Qed.

  Definition src_eq_size_of_arrivals_in_hyperperiod : Prop :=
    ltac:(body_of (fun s : S.statement_eq_size_of_arrivals_in_hyperperiod => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_eq_size_of_arrivals_in_hyperperiod : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_eq_size_of_arrivals_in_hyperperiod
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem eq_size_of_arrivals_in_hyperperiod_correspondence :
    PropSPropRel src_eq_size_of_arrivals_in_hyperperiod tgt_eq_size_of_arrivals_in_hyperperiod.
  Proof.
    fhyp_size_prefix Hts tsk.
    apply ar_forall_nat_correspondence. intros n1R n1L Hn1.
    apply ar_forall_nat_correspondence. intros n2R n2L Hn2.
    exact (sub_nat_eq_correspondence _ _ _ _
      (ari_size_related Job _ _ (JIH _ _ Hts _ _ (START _ _ Hts _ _ Hn1) tsk))
      (ari_size_related Job _ _ (JIH _ _ Hts _ _ (START _ _ Hts _ _ Hn2) tsk))).
  Qed.

  Definition src_job_in_hp_arrives_in_task_arrivals_up_to : Prop :=
    ltac:(body_of (fun s : S.statement_job_in_hp_arrives_in_task_arrivals_up_to => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_job_in_hp_arrives_in_task_arrivals_up_to : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_job_in_hp_arrives_in_task_arrivals_up_to
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem job_in_hp_arrives_in_task_arrivals_up_to_correspondence :
    PropSPropRel src_job_in_hp_arrives_in_task_arrivals_up_to tgt_job_in_hp_arrives_in_task_arrivals_up_to.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply fhyp_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (MEM tsk _ _ Hts)|].
    apply ar_imp_correspondence; [exact (VP tsk)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (LEO _ _ Hts j1)|].
    apply ar_imp_correspondence; [exact (LEO _ _ Hts j2)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (JMEM j _ _ (JIH _ _ Hts _ _ (START _ _ Hts _ _ (HPIDX _ _ Hts j2)) tsk))|].
    exact (JMEM j _ _ (task_arrivals_up_to_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _
      (@Lean.eq_refl _ _) (sub_add_correspondence _ _ _ _ (Hja j2) (HYP _ _ Hts)))).
  Qed.

  Definition src_job_in_own_hp : Prop :=
    ltac:(body_of (fun s : S.statement_job_in_own_hp => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_job_in_own_hp : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_job_in_own_hp Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem job_in_own_hp_correspondence : PropSPropRel src_job_in_own_hp tgt_job_in_own_hp.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply fhyp_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_periods_correspondence Task pR pL Hp tsR tsL Hts)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (MEM tsk _ _ Hts)|].
    apply ar_imp_correspondence; [exact (VP tsk)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (TSK j1 tsk)|].
    apply ar_imp_correspondence; [exact (LEO _ _ Hts j1)|].
    apply ar_imp_correspondence; [exact (LEO _ _ Hts j2)|].
    exact (JMEM j1 _ _ (JIH _ _ Hts _ _ (START _ _ Hts _ _ (HPIDX _ _ Hts j1)) tsk)).
  Qed.

  Ltac fhyp_corr_prefix Hts tsk j1 j2 :=
    apply ar_imp_correspondence; [exact VALID|];
    apply fhyp_forall_list_correspondence; intros ? ? Hts;
    apply ar_imp_correspondence; [exact (valid_periods_correspondence Task pR pL Hp _ _ Hts)|];
    apply ar_forall_identity_correspondence; intro tsk;
    apply ar_imp_correspondence; [exact (MEM tsk _ _ Hts)|];
    apply ar_imp_correspondence; [exact (VO tsk)|];
    apply ar_imp_correspondence; [exact (VP tsk)|];
    apply ar_imp_correspondence; [exact (RP tsk)|];
    apply ar_imp_correspondence; [exact INF|];
    apply ar_forall_identity_correspondence; intro j1;
    apply ar_forall_identity_correspondence; intro j2;
    apply ar_imp_correspondence; [exact (ARR j1)|];
    apply ar_imp_correspondence; [exact (TSK j1 tsk)|];
    apply ar_imp_correspondence; [exact (LEO _ _ Hts j1)|];
    apply ar_imp_correspondence; [exact (LEO _ _ Hts j2)|].

  Lemma fhyp_corr_job_related tsR tsL (Hts : ArListRel tsR tsL) (j1 j2 : Job) (tsk : Task) :
    Logic.eq (@S.corresponding_job_in_hyperperiod Task oR pR Job jtR jaR tsR arrR j1
        (@S.starting_instant_of_corresponding_hyperperiod Task oR pR Job jaR tsR j2) tsk)
      (I.Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod Task dT oL pL Job dJ jtL jaL
        tsL arrL j1 (I.Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod
          Task dT oL pL Job dJ jaL tsL j2) tsk).
  Proof.
    exact (imported_eq_to_coq_eq _ _ (corresponding_job_in_hyperperiod_correspondence Task Job oR oL Hoff
      pR pL Hp jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsR tsL Hts j1 _ _ tsk
      (starting_instant_of_corresponding_hyperperiod_correspondence Task Job oR oL Hoff pR pL Hp jaR jaL Hja
        tsR tsL Hts j2))).
  Qed.

  Definition src_corr_job_in_task_arrivals_up_to : Prop :=
    ltac:(body_of (fun s : S.statement_corr_job_in_task_arrivals_up_to => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_corr_job_in_task_arrivals_up_to : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_corr_job_in_task_arrivals_up_to
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem corr_job_in_task_arrivals_up_to_correspondence :
    PropSPropRel src_corr_job_in_task_arrivals_up_to tgt_corr_job_in_task_arrivals_up_to.
  Proof.
    fhyp_corr_prefix Hts tsk j1 j2.
    rewrite (fhyp_corr_job_related _ _ Hts j1 j2 tsk).
    exact (JMEM _ _ _ (task_arrivals_up_to_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _
      (@Lean.eq_refl _ _) (sub_add_correspondence _ _ _ _ (Hja j2) (HYP _ _ Hts)))).
  Qed.

  Definition src_corresponding_job_arrives : Prop :=
    ltac:(body_of (fun s : S.statement_corresponding_job_arrives => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_corresponding_job_arrives : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Hyperperiod_corresponding_job_arrives
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem corresponding_job_arrives_correspondence :
    PropSPropRel src_corresponding_job_arrives tgt_corresponding_job_arrives.
  Proof.
    fhyp_corr_prefix Hts tsk j1 j2.
    rewrite (fhyp_corr_job_related _ _ Hts j1 j2 tsk).
    exact (ARR _).
  Qed.
End Hyperperiod.
