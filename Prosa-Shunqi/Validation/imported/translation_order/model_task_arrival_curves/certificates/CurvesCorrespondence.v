From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.arrival.curves.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCurves ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence.

Module I := ImportedCurves.

(** Definition certificates for [model/task/arrival/curves.v]: for related
    inputs, each source definition and the compiled Lean definition are
    related.  Curve inputs are related pointwise on Nat ([SubNatFunRel]);
    every relation used as an input comes with import/export witnesses in both
    directions, so none of them is vacuous. *)

(** ** Curves on Nat: two-way coverage *)

Lemma cv_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Definition cv_import_fun (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun n => sub_nat_to_imported (fR (sub_nat_to_rocq n)).
Definition cv_export_fun (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun n => sub_nat_to_rocq (fL (sub_nat_to_imported n)).

Lemma cv_import_fun_rel fR : SubNatFunRel fR (cv_import_fun fR).
Proof.
  intros nR nL Hn. unfold SubNatRel, cv_import_fun.
  rewrite (cv_nat_input nR nL Hn). exact (@Lean.eq_refl _ _).
Qed.

Lemma cv_export_fun_rel fL : SubNatFunRel (cv_export_fun fL) fL.
Proof.
  intros nR nL Hn. unfold SubNatRel, cv_export_fun.
  exact (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _)
    (sub_imported_eq_congr fL _ _ Hn)).
Qed.

Theorem valid_arrival_curve_correspondence fR fL :
  SubNatFunRel fR fL ->
  PropSPropRel (@prosa.model.task.arrival.curves.valid_arrival_curve fR)
    (I.Prosa_Model_Task_Arrival_Curves_valid_arrival_curve fL).
Proof.
  intro Hf.
  unfold prosa.model.task.arrival.curves.valid_arrival_curve.
  cbn [I.Prosa_Model_Task_Arrival_Curves_valid_arrival_curve].
  apply ar_and_correspondence.
  - exact (sub_nat_eq_correspondence _ _ _ _
      (Hf O Lean.Nat_zero (sub_nat_rel_canonical O)) (sub_nat_rel_canonical O)).
  - unfold prosa.util.rel.monotone. cbn [I.Prosa_Util_Rel_monotone].
    apply ar_forall_nat_correspondence => xR xL Hx.
    apply ar_forall_nat_correspondence => yR yL Hy.
    apply ar_imp_correspondence.
    + exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ Hx Hy)).
    + exact (ar_bool_truth_correspondence _ _
        (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy))).
Qed.

Section Curves.
  Context (Task Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let NUM tsk t1R t1L t2R t2L H1 H2 :=
    number_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr
      tsk tsk t1R t1L t2R t2L (@Lean.eq_refl _ tsk) H1 H2.

  Theorem respects_max_arrivals_correspondence (tsk : Task) fR fL :
    SubNatFunRel fR fL ->
    PropSPropRel
      (@prosa.model.task.arrival.curves.respects_max_arrivals Task Job jtR arrR tsk fR)
      (I.Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task dT Job dJ jtL arrL tsk fL).
  Proof.
    intro Hf.
    unfold prosa.model.task.arrival.curves.respects_max_arrivals.
    cbn [I.Prosa_Model_Task_Arrival_Curves_respects_max_arrivals].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _ (NUM tsk _ _ _ _ H1 H2)
      (Hf _ _ (ari_nat_sub_related _ _ _ _ H2 H1))).
  Qed.

  Theorem respects_min_arrivals_correspondence (tsk : Task) fR fL :
    SubNatFunRel fR fL ->
    PropSPropRel
      (@prosa.model.task.arrival.curves.respects_min_arrivals Task Job jtR arrR tsk fR)
      (I.Prosa_Model_Task_Arrival_Curves_respects_min_arrivals Task dT Job dJ jtL arrL tsk fL).
  Proof.
    intro Hf.
    unfold prosa.model.task.arrival.curves.respects_min_arrivals.
    cbn [I.Prosa_Model_Task_Arrival_Curves_respects_min_arrivals].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (Hf _ _ (ari_nat_sub_related _ _ _ _ H2 H1)) (NUM tsk _ _ _ _ H1 H2)).
  Qed.

  Theorem respects_min_separation_correspondence (tsk : Task) fR fL :
    SubNatFunRel fR fL ->
    PropSPropRel
      (@prosa.model.task.arrival.curves.respects_min_separation Task Job jtR arrR tsk fR)
      (I.Prosa_Model_Task_Arrival_Curves_respects_min_separation Task dT Job dJ jtL arrL tsk fL).
  Proof.
    intro Hf.
    unfold prosa.model.task.arrival.curves.respects_min_separation.
    cbn [I.Prosa_Model_Task_Arrival_Curves_respects_min_separation].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (Hf _ _ (NUM tsk _ _ _ _ H1 H2)) (ari_nat_sub_related _ _ _ _ H2 H1)).
  Qed.

  Theorem respects_max_separation_correspondence (tsk : Task) fR fL :
    SubNatFunRel fR fL ->
    PropSPropRel
      (@prosa.model.task.arrival.curves.respects_max_separation Task Job jtR arrR tsk fR)
      (I.Prosa_Model_Task_Arrival_Curves_respects_max_separation Task dT Job dJ jtL arrL tsk fL).
  Proof.
    intro Hf.
    unfold prosa.model.task.arrival.curves.respects_max_separation.
    cbn [I.Prosa_Model_Task_Arrival_Curves_respects_max_separation].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (ari_nat_sub_related _ _ _ _ H2 H1) (Hf _ _ (NUM tsk _ _ _ _ H1 H2))).
  Qed.
End Curves.

(** ** Task-set level (the four curve classes are input relations with
    two-way coverage) *)

Section TaskSet.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition CvCurveFamilyRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
    forall tsk : Task, SubNatFunRel (fR tsk) (fL tsk).

  Lemma cv_family_import fR : CvCurveFamilyRel fR (fun tsk => cv_import_fun (fR tsk)).
  Proof. intro tsk. exact (cv_import_fun_rel _). Qed.
  Lemma cv_family_export fL : CvCurveFamilyRel (fun tsk => cv_export_fun (fL tsk)) fL.
  Proof. intro tsk. exact (cv_export_fun_rel _). Qed.

  Definition CvMaxArrivalsRel (cR : prosa.model.task.arrival.curves.MaxArrivals Task)
      (cL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    CvCurveFamilyRel (@prosa.model.task.arrival.curves.max_arrivals Task cR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL).
  Definition CvMinArrivalsRel (cR : prosa.model.task.arrival.curves.MinArrivals Task)
      (cL : I.Prosa_Model_Task_Arrival_Curves_MinArrivals Task dT) : SProp :=
    CvCurveFamilyRel (@prosa.model.task.arrival.curves.min_arrivals Task cR)
      (I.Prosa_Model_Task_Arrival_Curves_MinArrivals_min_arrivals Task dT cL).
  Definition CvMaxSeparationRel (cR : prosa.model.task.arrival.curves.MaxSeparation Task)
      (cL : I.Prosa_Model_Task_Arrival_Curves_MaxSeparation Task dT) : SProp :=
    CvCurveFamilyRel (@prosa.model.task.arrival.curves.max_separation Task cR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxSeparation_max_separation Task dT cL).
  Definition CvMinSeparationRel (cR : prosa.model.task.arrival.curves.MinSeparation Task)
      (cL : I.Prosa_Model_Task_Arrival_Curves_MinSeparation Task dT) : SProp :=
    CvCurveFamilyRel (@prosa.model.task.arrival.curves.min_separation Task cR)
      (I.Prosa_Model_Task_Arrival_Curves_MinSeparation_min_separation Task dT cL).

  (** Class carriers: every source instance has a related compiled instance
      and conversely. *)
  Lemma MaxArrivals_source_total cR : CvMaxArrivalsRel cR
    (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT (fun tsk => cv_import_fun (cR tsk))).
  Proof. exact (cv_family_import _). Qed.
  Lemma MaxArrivals_target_total cL : CvMaxArrivalsRel
    (fun tsk => cv_export_fun (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk)) cL.
  Proof. exact (cv_family_export _). Qed.
  Lemma MinArrivals_source_total cR : CvMinArrivalsRel cR
    (I.Prosa_Model_Task_Arrival_Curves_MinArrivals_mk Task dT (fun tsk => cv_import_fun (cR tsk))).
  Proof. exact (cv_family_import _). Qed.
  Lemma MinArrivals_target_total cL : CvMinArrivalsRel
    (fun tsk => cv_export_fun (I.Prosa_Model_Task_Arrival_Curves_MinArrivals_min_arrivals Task dT cL tsk)) cL.
  Proof. exact (cv_family_export _). Qed.
  Lemma MaxSeparation_source_total cR : CvMaxSeparationRel cR
    (I.Prosa_Model_Task_Arrival_Curves_MaxSeparation_mk Task dT (fun tsk => cv_import_fun (cR tsk))).
  Proof. exact (cv_family_import _). Qed.
  Lemma MaxSeparation_target_total cL : CvMaxSeparationRel
    (fun tsk => cv_export_fun (I.Prosa_Model_Task_Arrival_Curves_MaxSeparation_max_separation Task dT cL tsk)) cL.
  Proof. exact (cv_family_export _). Qed.
  Lemma MinSeparation_source_total cR : CvMinSeparationRel cR
    (I.Prosa_Model_Task_Arrival_Curves_MinSeparation_mk Task dT (fun tsk => cv_import_fun (cR tsk))).
  Proof. exact (cv_family_import _). Qed.
  Lemma MinSeparation_target_total cL : CvMinSeparationRel
    (fun tsk => cv_export_fun (I.Prosa_Model_Task_Arrival_Curves_MinSeparation_min_separation Task dT cL tsk)) cL.
  Proof. exact (cv_family_export _). Qed.

  Theorem valid_taskset_arrival_curve_correspondence tsR tsL aR aL :
    ArListRel tsR tsL -> CvCurveFamilyRel aR aL ->
    PropSPropRel
      (@prosa.model.task.arrival.curves.valid_taskset_arrival_curve Task tsR aR)
      (I.Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task dT tsL aL).
  Proof.
    intros Hts Ha.
    unfold prosa.model.task.arrival.curves.valid_taskset_arrival_curve.
    cbn [I.Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve].
    apply ar_forall_identity_correspondence => tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (valid_arrival_curve_correspondence _ _ (Ha tsk)).
  Qed.

  Section WithJobs.
    Context (Job : eqType).
    Let dJ := ar_decidable_eq Job.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
    Variable tsR : prosa.model.task.concept.TaskSet Task.
    Variable tsL : I.Prosa_Model_Task_Concept_TaskSet Task.
    Hypothesis Hts : ArListRel tsR tsL.

    Let MEM tsk := ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts).

    Theorem taskset_respects_max_arrivals_correspondence cR cL :
      CvMaxArrivalsRel cR cL ->
      PropSPropRel
        (@prosa.model.task.arrival.curves.taskset_respects_max_arrivals Task Job jtR arrR cR tsR)
        (I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task dT Job dJ jtL arrL cL tsL).
    Proof.
      intro Hc.
      unfold prosa.model.task.arrival.curves.taskset_respects_max_arrivals.
      cbn [I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|].
      exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hc tsk)).
    Qed.

    Theorem taskset_respects_min_arrivals_correspondence cR cL :
      CvMinArrivalsRel cR cL ->
      PropSPropRel
        (@prosa.model.task.arrival.curves.taskset_respects_min_arrivals Task Job jtR arrR cR tsR)
        (I.Prosa_Model_Task_Arrival_Curves_taskset_respects_min_arrivals Task dT Job dJ jtL arrL cL tsL).
    Proof.
      intro Hc.
      unfold prosa.model.task.arrival.curves.taskset_respects_min_arrivals.
      cbn [I.Prosa_Model_Task_Arrival_Curves_taskset_respects_min_arrivals].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|].
      exact (respects_min_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hc tsk)).
    Qed.

    Theorem taskset_respects_max_separation_correspondence cR cL :
      CvMaxSeparationRel cR cL ->
      PropSPropRel
        (@prosa.model.task.arrival.curves.taskset_respects_max_separation Task Job jtR arrR cR tsR)
        (I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_separation Task dT Job dJ jtL arrL cL tsL).
    Proof.
      intro Hc.
      unfold prosa.model.task.arrival.curves.taskset_respects_max_separation.
      cbn [I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_separation].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|].
      exact (respects_max_separation_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hc tsk)).
    Qed.

    Theorem taskset_respects_min_separation_correspondence cR cL :
      CvMinSeparationRel cR cL ->
      PropSPropRel
        (@prosa.model.task.arrival.curves.taskset_respects_min_separation Task Job jtR arrR cR tsR)
        (I.Prosa_Model_Task_Arrival_Curves_taskset_respects_min_separation Task dT Job dJ jtL arrL cL tsL).
    Proof.
      intro Hc.
      unfold prosa.model.task.arrival.curves.taskset_respects_min_separation.
      cbn [I.Prosa_Model_Task_Arrival_Curves_taskset_respects_min_separation].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|].
      exact (respects_min_separation_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hc tsk)).
    Qed.
  End WithJobs.
End TaskSet.
