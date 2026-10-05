From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsDelayPropagationSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsDelayPropagation ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence DelayPropagationCorrespondence CurvesCorrespondence.

Module I := ImportedFactsDelayPropagation.
Module S := FactsDelayPropagationSemanticSource.FactsDelayPropagationSemanticSource.

(** Statement correspondences for [analysis/facts/delay_propagation.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading input binders (task/job types, job-task maps, the two
    [JobArrival] instances, the mapping functions, delay functions, the task
    set and, where it precedes every hypothesis, the type-one arrival
    sequence); target side: the type of the imported Lean theorem.  The
    mapping functions [job1_of]/[task1_of] are the same functions on both
    sides (identity carriers); [job2_of] is related pointwise by [ArListRel];
    delays pointwise on Nat; arrival sequences, task sets and the type-one
    arrival curve after a hypothesis are covered in both directions.  The
    definition-level relations are the accepted delay-propagation and curves
    certificates. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** List helpers *)

Fixpoint fdp_map_canonical (A B : Type) (f : A -> B) (xs : seq A) {struct xs} :
    Lean.eq (ar_list_to_imported (map f xs)) (I.List_map A B f (ar_list_to_imported xs)) :=
  match xs return Lean.eq (ar_list_to_imported (map f xs)) (I.List_map A B f (ar_list_to_imported xs)) with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons B (f x)) _ _ (fdp_map_canonical A B f tail)
  end.

Lemma fdp_map_related (A B : Type) (f : A -> B) xsR xsL :
  ArListRel xsR xsL -> ArListRel (map f xsR) (I.List_map A B f xsL).
Proof.
  intro Hxs.
  refine (ari_lean_transport (fun l => ArListRel _ (I.List_map A B f l)) _ _ Hxs _).
  exact (fdp_map_canonical A B f xsR).
Qed.

Lemma fdp_mem_truth (T : eqType) (x : T) xsR xsL :
  ArListRel xsR xsL ->
  PropSPropRel (is_true (x \in xsR)) (Lean.eq (ar_target_decide_mem T x xsL) I.Bool_true).
Proof. intro H. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related T x xsR xsL H)). Qed.

Lemma fdp_range_le_lt aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (leq aR bR && ltn bR cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_lt bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc. apply ar_bool_truth_correspondence.
  exact (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
    (ar_decide_lt_related _ _ _ _ Hb Hc)).
Qed.

Lemma fdp_forall_family (Task : eqType)
    (PR : prosa.model.task.arrival.curves.MaxArrivals Task -> Prop)
    (PL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task (ar_decidable_eq Task) -> SProp) :
  (forall cR cL, CvMaxArrivalsRel Task cR cL -> PropSPropRel (PR cR) (PL cL)) ->
  PropSPropRel (forall cR, PR cR) (forall cL, PL cL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR cL. exact (prop_to_sprop _ _ (H _ _ (MaxArrivals_target_total Task cL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro cR.
    exact (sprop_to_prop _ _ (H _ _ (MaxArrivals_source_total Task cR)) (HL _)).
Qed.

Section FDP.
  Context (Task1 Task2 Job1 Job2 : eqType).
  Let dT1 := ar_decidable_eq Task1.
  Let dT2 := ar_decidable_eq Task2.
  Let dJ1 := ar_decidable_eq Job1.
  Let dJ2 := ar_decidable_eq Job2.
  Variable jt1R : prosa.model.task.concept.JobTask Job1 Task1.
  Variable jt1L : I.Prosa_Model_Task_Concept_JobTask Job1 dJ1 Task1 dT1.
  Hypothesis Hjt1 : forall j : Job1,
    Lean.eq (@prosa.model.task.concept.job_task Job1 Task1 jt1R j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job1 dJ1 Task1 dT1 jt1L j).
  Variable jt2R : prosa.model.task.concept.JobTask Job2 Task2.
  Variable jt2L : I.Prosa_Model_Task_Concept_JobTask Job2 dJ2 Task2 dT2.
  Hypothesis Hjt2 : forall j : Job2,
    Lean.eq (@prosa.model.task.concept.job_task Job2 Task2 jt2R j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job2 dJ2 Task2 dT2 jt2L j).
  Variable ja1R : prosa.behavior.job.JobArrival Job1.
  Variable ja1L : I.Prosa_Behavior_Job_JobArrival Job1 dJ1.
  Hypothesis Hja1 : ArJobArrivalRel Job1 ja1R ja1L.
  Variable ja2R : prosa.behavior.job.JobArrival Job2.
  Variable ja2L : I.Prosa_Behavior_Job_JobArrival Job2 dJ2.
  Hypothesis Hja2 : ArJobArrivalRel Job2 ja2R ja2L.
  Variable job1_of : Job2 -> Job1.
  Variable task1_of : Task2 -> Task1.
  Variable job2_ofR : Job1 -> seq Job2.
  Variable job2_ofL : Job1 -> I.List Job2.
  Hypothesis Hj2 : forall j, ArListRel (job2_ofR j) (job2_ofL j).
  Variable adR : Job2 -> nat.
  Variable adL : Job2 -> Lean.Nat.
  Hypothesis Had : forall j, SubNatRel (adR j) (adL j).
  Variable dbR : Task2 -> nat.
  Variable dbL : Task2 -> Lean.Nat.
  Hypothesis Hdb : forall tsk, SubNatRel (dbR tsk) (dbL tsk).
  Variable tsR : seq Task2.
  Variable tsL : I.List Task2.
  Hypothesis Hts : ArListRel tsR tsL.

  Let PROP arrR arrL Harr : ArArrivalSequenceRel Job2
      (@prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence Job1 Job2 ja1R job1_of arrR job2_ofR adR)
      (I.Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2 dJ1 dJ2 ja1L job1_of arrL job2_ofL adL) :=
    fun tR tL Ht => propagated_arrival_sequence_correspondence Job1 Job2 ja1R ja1L Hja1 job1_of arrR arrL Harr
      job2_ofR job2_ofL Hj2 adR adL Had tR tL Ht.
  Let VASM arrR arrL Harr :=
    valid_arr_seq_propagation_mapping_correspondence Task2 Job1 Job2 jt2R jt2L Hjt2 ja1R ja1L Hja1
      ja2R ja2L Hja2 job1_of dbR dbL Hdb arrR arrL Harr job2_ofR job2_ofL Hj2 adR adL Had tsR tsL Hts.
  Let VDPM :=
    valid_delay_propagation_mapping_correspondence Task1 Task2 Job1 Job2 jt1R jt1L Hjt1 jt2R jt2L Hjt2
      ja1R ja1L Hja1 ja2R ja2L Hja2 job1_of task1_of dbR dbL Hdb tsR tsL Hts.
  Let TAB2 arrR arrL Harr tsk t1R t1L t2R t2L H1 H2 :=
    task_arrivals_between_correspondence Job2 Task2 jt2R jt2L Hjt2 _ _ (PROP arrR arrL Harr)
      tsk tsk t1R t1L t2R t2L (@Lean.eq_refl _ tsk) H1 H2.
  Let MEM2 tsk := fdp_mem_truth Task2 tsk _ _ Hts.
  Let TS1 := fdp_map_related Task2 Task1 task1_of _ _ Hts.

  Section WithArr.
    Variable arr1R : prosa.behavior.arrival_sequence.arrival_sequence Job1.
    Variable arr1L : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job1 dJ1.
    Hypothesis Harr1 : ArArrivalSequenceRel Job1 arr1R arr1L.
    Let P2 := PROP arr1R arr1L Harr1.
    Definition src_consistent_propagated_arrival_sequence : Prop := ltac:(body_of (fun s : S.statement_consistent_propagated_arrival_sequence => s Task2 Job1 Job2 jt2R ja1R ja2R job1_of job2_ofR adR dbR tsR arr1R)).
    Definition tgt_consistent_propagated_arrival_sequence : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_consistent_propagated_arrival_sequence Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of job2_ofL adL dbL tsL arr1L)).
    Theorem consistent_propagated_arrival_sequence_correspondence : PropSPropRel src_consistent_propagated_arrival_sequence tgt_consistent_propagated_arrival_sequence.
    Proof.
      apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
      exact (consistent_arrival_times_correspondence_certificate Job2 ja2R ja2L _ _ Hja2 P2).
    Qed.

    Definition src_propagated_arrival_sequence_uniq : Prop := ltac:(body_of (fun s : S.statement_propagated_arrival_sequence_uniq => s Task2 Job1 Job2 jt2R ja1R ja2R job1_of job2_ofR adR dbR tsR arr1R)).
    Definition tgt_propagated_arrival_sequence_uniq : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_propagated_arrival_sequence_uniq Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of job2_ofL adL dbL tsL arr1L)).
    Theorem propagated_arrival_sequence_uniq_correspondence : PropSPropRel src_propagated_arrival_sequence_uniq tgt_propagated_arrival_sequence_uniq.
    Proof.
      apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
      apply ar_imp_correspondence;
        [exact (valid_arrival_sequence_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
      exact (arrival_sequence_uniq_correspondence_certificate Job2 _ _ P2).
    Qed.

    Definition src_valid_propagated_arrival_sequence : Prop := ltac:(body_of (fun s : S.statement_valid_propagated_arrival_sequence => s Task2 Job1 Job2 jt2R ja1R ja2R job1_of job2_ofR adR dbR tsR arr1R)).
    Definition tgt_valid_propagated_arrival_sequence : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_valid_propagated_arrival_sequence Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of job2_ofL adL dbL tsL arr1L)).
    Theorem valid_propagated_arrival_sequence_correspondence : PropSPropRel src_valid_propagated_arrival_sequence tgt_valid_propagated_arrival_sequence.
    Proof.
      apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
      apply ar_imp_correspondence;
        [exact (valid_arrival_sequence_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
      exact (valid_arrival_sequence_correspondence_certificate Job2 ja2R ja2L _ _ Hja2 P2).
    Qed.

    Definition src_arrives_in_propagated_if : Prop := ltac:(body_of (fun s : S.statement_arrives_in_propagated_if => s Task2 Job1 Job2 jt2R ja1R ja2R job1_of job2_ofR adR dbR tsR arr1R)).
    Definition tgt_arrives_in_propagated_if : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_arrives_in_propagated_if Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of job2_ofL adL dbL tsL arr1L)).
    Theorem arrives_in_propagated_if_correspondence : PropSPropRel src_arrives_in_propagated_if tgt_arrives_in_propagated_if.
    Proof.
      apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
      apply ar_forall_identity_correspondence => j2.
      apply ar_imp_correspondence;
        [exact (consistent_arrival_times_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job1 _ _ (job1_of j2) Harr1)|].
      exact (arrives_in_correspondence_certificate Job2 _ _ j2 P2).
    Qed.

    Definition src_arrives_in_propagated_only_if : Prop := ltac:(body_of (fun s : S.statement_arrives_in_propagated_only_if => s Task2 Job1 Job2 jt2R ja1R ja2R job1_of job2_ofR adR dbR tsR arr1R)).
    Definition tgt_arrives_in_propagated_only_if : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_arrives_in_propagated_only_if Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of job2_ofL adL dbL tsL arr1L)).
    Theorem arrives_in_propagated_only_if_correspondence : PropSPropRel src_arrives_in_propagated_only_if tgt_arrives_in_propagated_only_if.
    Proof.
      apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
      apply ar_forall_identity_correspondence => j2.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job2 _ _ j2 P2)|].
      exact (arrives_in_correspondence_certificate Job1 _ _ (job1_of j2) Harr1).
    Qed.

    Definition src_trigger_job_arrival_bounded : Prop := ltac:(body_of (fun s : S.statement_trigger_job_arrival_bounded => s Task2 Job1 Job2 jt2R ja1R ja2R job1_of job2_ofR adR dbR tsR arr1R)).
    Definition tgt_trigger_job_arrival_bounded : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_trigger_job_arrival_bounded Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of job2_ofL adL dbL tsL arr1L)).
    Theorem trigger_job_arrival_bounded_correspondence : PropSPropRel src_trigger_job_arrival_bounded tgt_trigger_job_arrival_bounded.
    Proof.
      apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_identity_correspondence => tsk2.
      apply ar_imp_correspondence; [exact (MEM2 tsk2)|].
      apply ar_forall_identity_correspondence => j1.
      apply ar_imp_correspondence;
        [exact (fdp_mem_truth Job1 j1 _ _ (fdp_map_related Job2 Job1 job1_of _ _
          (TAB2 _ _ Harr1 tsk2 _ _ _ _ H1 H2)))|].
      exact (fdp_range_le_lt _ _ _ _ _ _ (ari_nat_sub_related _ _ _ _ H1 (Hdb tsk2)) (Hja1 j1) H2).
    Qed.
  End WithArr.

  (** Hypotheses of the correctness statements (type-one arrival sequence
      covered in both directions). *)
  Let SING : PropSPropRel
      (forall tsk1 : Task1, tsk1 \in [seq task1_of tsk2 | tsk2 <- tsR] ->
        forall j1 : Job1, @prosa.model.task.concept.job_task Job1 Task1 jt1R j1 = tsk1 -> is_true (leq (size (job2_ofR j1)) (S O)))
      (forall tsk1 : Task1,
        Lean.eq (ar_target_decide_mem Task1 tsk1 (I.List_map Task2 Task1 task1_of tsL)) I.Bool_true ->
        forall j1 : Job1,
          Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job1 dJ1 Task1 dT1 jt1L j1) tsk1 ->
          sub_imported_le (I.List_length Job2 (job2_ofL j1)) (Lean.Nat_succ Lean.Nat_zero)).
  Proof.
    apply ar_forall_identity_correspondence => tsk1.
    apply ar_imp_correspondence; [exact (fdp_mem_truth Task1 tsk1 _ _ TS1)|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence.
    - apply prop_sprop_rel_intro.
      + intro H. exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (Hjt1 j1)) (coq_eq_to_imported_eq _ _ H)).
      + intro H. apply strictly_inhabits.
        exact (imported_eq_to_coq_eq _ _ (sub_imported_eq_trans _ _ _ (Hjt1 j1) H)).
    - exact (sub_nat_le_correspondence _ _ _ _ (ari_size_related Job2 _ _ (Hj2 j1)) (sub_nat_rel_canonical (S O))).
  Qed.

  Definition src_subset_trigger_jobs : Prop := ltac:(body_of (fun s : S.statement_subset_trigger_jobs => s Task1 Task2 Job1 Job2 jt1R jt2R ja1R ja2R job1_of task1_of job2_ofR adR dbR tsR)).
  Definition tgt_subset_trigger_jobs : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_subset_trigger_jobs Task1 Task2 dT1 dT2 Job1 Job2 dJ1 dJ2 jt1L jt2L ja1L ja2L job1_of task1_of job2_ofL adL dbL tsL)).
  Theorem subset_trigger_jobs_correspondence : PropSPropRel src_subset_trigger_jobs tgt_subset_trigger_jobs.
  Proof.
    apply ar_imp_correspondence; [exact VDPM|].
    apply (dp_forall_arrival_sequence Job1) => arr1R arr1L Harr1.
    apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    apply ar_forall_identity_correspondence => tsk2.
    apply ar_imp_correspondence; [exact (MEM2 tsk2)|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence;
      [exact (fdp_mem_truth Job1 j1 _ _ (fdp_map_related Job2 Job1 job1_of _ _
        (TAB2 _ _ Harr1 tsk2 _ _ _ _ H1 H2)))|].
    exact (fdp_mem_truth Job1 j1 _ _ (task_arrivals_between_correspondence Job1 Task1 jt1R jt1L Hjt1 _ _ Harr1
      (task1_of tsk2) (task1_of tsk2) _ _ _ _ (@Lean.eq_refl _ _) (ari_nat_sub_related _ _ _ _ H1 (Hdb tsk2)) H2)).
  Qed.

  Definition src_job1_of_inj : Prop := ltac:(body_of (fun s : S.statement_job1_of_inj => s Task1 Task2 Job1 Job2 jt1R jt2R ja1R ja2R job1_of task1_of job2_ofR adR dbR tsR)).
  Definition tgt_job1_of_inj : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_job1_of_inj Task1 Task2 dT1 dT2 Job1 Job2 dJ1 dJ2 jt1L jt2L ja1L ja2L job1_of task1_of job2_ofL adL dbL tsL)).
  Theorem job1_of_inj_correspondence : PropSPropRel src_job1_of_inj tgt_job1_of_inj.
  Proof.
    apply ar_imp_correspondence; [exact VDPM|].
    apply (dp_forall_arrival_sequence Job1) => arr1R arr1L Harr1.
    apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
    apply ar_imp_correspondence; [exact SING|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => tsk2.
    apply ar_imp_correspondence; [exact (MEM2 tsk2)|].
    apply ar_forall_identity_correspondence => x.
    apply ar_forall_identity_correspondence => y.
    have T2 := TAB2 _ _ Harr1 tsk2 _ _ _ _ H1 H2.
    apply ar_imp_correspondence; [exact (fdp_mem_truth Job2 x _ _ T2)|].
    apply ar_imp_correspondence; [exact (fdp_mem_truth Job2 y _ _ T2)|].
    apply ar_imp_correspondence; [exact (dp_eq_correspondence Job1 _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _))|].
    exact (dp_eq_correspondence Job2 _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  Qed.

  Definition src_uniq_trigger_jobs : Prop := ltac:(body_of (fun s : S.statement_uniq_trigger_jobs => s Task1 Task2 Job1 Job2 jt1R jt2R ja1R ja2R job1_of task1_of job2_ofR adR dbR tsR)).
  Definition tgt_uniq_trigger_jobs : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_uniq_trigger_jobs Task1 Task2 dT1 dT2 Job1 Job2 dJ1 dJ2 jt1L jt2L ja1L ja2L job1_of task1_of job2_ofL adL dbL tsL)).
  Theorem uniq_trigger_jobs_correspondence : PropSPropRel src_uniq_trigger_jobs tgt_uniq_trigger_jobs.
  Proof.
    apply ar_imp_correspondence; [exact VDPM|].
    apply (dp_forall_arrival_sequence Job1) => arr1R arr1L Harr1.
    apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
    apply ar_imp_correspondence; [exact SING|].
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => tsk2.
    apply ar_imp_correspondence; [exact (MEM2 tsk2)|].
    exact (ar_uniq_correspondence Job1 _ _ (fdp_map_related Job2 Job1 job1_of _ _
      (TAB2 _ _ Harr1 tsk2 _ _ _ _ H1 H2))).
  Qed.

  Definition src_trigger_job_size : Prop := ltac:(body_of (fun s : S.statement_trigger_job_size => s Task1 Task2 Job1 Job2 jt1R jt2R ja1R ja2R job1_of task1_of job2_ofR adR dbR tsR)).
  Definition tgt_trigger_job_size : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_trigger_job_size Task1 Task2 dT1 dT2 Job1 Job2 dJ1 dJ2 jt1L jt2L ja1L ja2L job1_of task1_of job2_ofL adL dbL tsL)).
  Theorem trigger_job_size_correspondence : PropSPropRel src_trigger_job_size tgt_trigger_job_size.
  Proof.
    apply ar_imp_correspondence; [exact VDPM|].
    apply (dp_forall_arrival_sequence Job1) => arr1R arr1L Harr1.
    apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
    apply ar_imp_correspondence; [exact SING|].
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    apply ar_forall_identity_correspondence => tsk2.
    apply ar_imp_correspondence; [exact (MEM2 tsk2)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (ari_size_related Job1 _ _ (fdp_map_related Job2 Job1 job1_of _ _ (TAB2 _ _ Harr1 tsk2 _ _ _ _ H1 H2)))
      (ari_size_related Job1 _ _ (task_arrivals_between_correspondence Job1 Task1 jt1R jt1L Hjt1 _ _ Harr1
        (task1_of tsk2) (task1_of tsk2) _ _ _ _ (@Lean.eq_refl _ _) (ari_nat_sub_related _ _ _ _ H1 (Hdb tsk2)) H2))).
  Qed.

  (** The propagated arrival curve ([max_arrivals2], via the source-local
      [propagated_arrival_curve]) for related type-one curves. *)
  Lemma fdp_max_arrivals2_related maR maL :
    CvMaxArrivalsRel Task1 maR maL ->
    CvMaxArrivalsRel Task2 (@S.max_arrivals2 Task1 Task2 task1_of dbR maR)
      (I.Prosa_Analysis_Facts_DelayPropagation_max_arrivals2 Task1 Task2 dT1 dT2 task1_of dbL maL).
  Proof.
    intros Hma tsk2 nR nL Hn.
    refine (ari_lean_transport (fun x => SubNatRel _ (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task2 dT2
      (I.Prosa_Analysis_Facts_DelayPropagation_max_arrivals2 Task1 Task2 dT1 dT2 task1_of dbL maL) tsk2 x)) _ _ Hn _).
    destruct nR as [|n].
    - exact (@Lean.eq_refl _ _).
    - exact (Hma (task1_of tsk2) _ _ (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical n.+1) (Hdb tsk2))).
  Qed.

  Definition src_propagated_arrival_curve_valid : Prop := ltac:(body_of (fun s : S.statement_propagated_arrival_curve_valid => s Task1 Task2 task1_of dbR tsR)).
  Definition tgt_propagated_arrival_curve_valid : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_propagated_arrival_curve_valid Task1 Task2 dT1 dT2 task1_of dbL tsL)).
  Theorem propagated_arrival_curve_valid_correspondence : PropSPropRel src_propagated_arrival_curve_valid tgt_propagated_arrival_curve_valid.
  Proof.
    apply fdp_forall_family => maR maL Hma.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence => tsk2.
      apply ar_imp_correspondence; [exact (MEM2 tsk2)|].
      unfold prosa.util.rel.monotone. cbn [I.Prosa_Util_Rel_monotone].
      apply ar_forall_nat_correspondence => xR xL Hx.
      apply ar_forall_nat_correspondence => yR yL Hy.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ Hx Hy))|].
      exact (ar_bool_truth_correspondence _ _
        (ar_decide_le_related _ _ _ _ (Hma (task1_of tsk2) _ _ Hx) (Hma (task1_of tsk2) _ _ Hy))).
    - exact (valid_taskset_arrival_curve_correspondence Task2 tsR tsL _ _ Hts (fdp_max_arrivals2_related maR maL Hma)).
  Qed.

  Definition src_propagated_arrival_curve_respected : Prop := ltac:(body_of (fun s : S.statement_propagated_arrival_curve_respected => s Task1 Task2 Job1 Job2 jt1R jt2R ja1R ja2R job1_of task1_of job2_ofR adR dbR tsR)).
  Definition tgt_propagated_arrival_curve_respected : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_DelayPropagation_propagated_arrival_curve_respected Task1 Task2 dT1 dT2 Job1 Job2 dJ1 dJ2 jt1L jt2L ja1L ja2L job1_of task1_of job2_ofL adL dbL tsL)).
  Theorem propagated_arrival_curve_respected_correspondence : PropSPropRel src_propagated_arrival_curve_respected tgt_propagated_arrival_curve_respected.
  Proof.
    apply ar_imp_correspondence; [exact VDPM|].
    apply fdp_forall_family => maR maL Hma.
    apply (dp_forall_arrival_sequence Job1) => arr1R arr1L Harr1.
    apply ar_imp_correspondence; [exact (VASM _ _ Harr1)|].
    apply ar_imp_correspondence; [exact SING|].
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job1 ja1R ja1L _ _ Hja1 Harr1)|].
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task1 _ _ _ _ TS1 Hma)|].
    apply ar_imp_correspondence;
      [exact (taskset_respects_max_arrivals_correspondence Task1 Job1 jt1R jt1L Hjt1 _ _ Harr1 _ _ TS1 _ _ Hma)|].
    exact (taskset_respects_max_arrivals_correspondence Task2 Job2 jt2R jt2L Hjt2 _ _ (PROP _ _ Harr1) _ _ Hts _ _
      (fdp_max_arrivals2_related maR maL Hma)).
  Qed.
End FDP.
