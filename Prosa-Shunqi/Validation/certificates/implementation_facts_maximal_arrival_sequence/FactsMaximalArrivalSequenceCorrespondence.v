From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsMaximalArrivalSequenceSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsMaximalArrivalSequence ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence CurvesCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  MaximalArrivalSequenceCorrespondence.

Module I := ImportedFactsMaximalArrivalSequence.
Module S := FactsMaximalArrivalSequenceSemanticSource.FactsMaximalArrivalSequenceSemanticSource.

(** Statement correspondences for
    [implementation/facts/maximal_arrival_sequence.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading job/task types and the job/task classes that precede the task
    set; target side: the type of the imported Lean theorem at related class
    inputs ([TaskCost]/[JobCost] pointwise by [SubNatRel], [job_task] by
    [Lean.eq], [job_arrival] by the accepted [ArJobArrivalRel]).  All later
    binders are covered in both directions: the task set by [ArListRel], the
    [MaxArrivals] class by the accepted [CvMaxArrivalsRel] totals, the job
    generator by the accepted [MsGeneratorRel] totals, and Nats by
    [ar_forall_nat_correspondence].  The definitions are closed by the
    accepted maximal-arrival-sequence, arrivals and curves correspondences;
    the two structurally identical list encodings of the replayed adapters
    are identified by a proved bridge. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic lemmas (proved) *)

Lemma fma_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma fma_eq_correspondence (T : Type) (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hy)))).
Qed.

Lemma fma_list_bridge (T : Type) (xs : seq T) :
  Logic.eq (svc_list_to_imported xs) (ar_list_to_imported xs).
Proof. induction xs as [|x xs IH]; cbn; [reflexivity | by rewrite IH]. Qed.

Lemma fma_svc_to_ar (T : Type) (xsR : seq T) (xsL : I.List T) :
  SvcListRel xsR xsL -> ArListRel xsR xsL.
Proof.
  intro H. unfold ArListRel.
  exact (sub_imported_eq_trans _ _ _
    (ms_logic_eq_to_lean_eq _ _ (Logic.eq_sym (fma_list_bridge T xsR))) H).
Qed.

Lemma fma_ar_to_svc (T : Type) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> SvcListRel xsR xsL.
Proof.
  intro H. unfold SvcListRel.
  exact (sub_imported_eq_trans _ _ _
    (ms_logic_eq_to_lean_eq _ _ (fma_list_bridge T xsR)) H).
Qed.

Lemma fma_list_source_total (T : Type) (xs : seq T) : ArListRel xs (ar_list_to_imported xs).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma fma_list_target_total (T : Type) (xs : I.List T) : ArListRel (ar_list_to_rocq xs) xs.
Proof. exact (ar_list_target_roundtrip xs). Qed.

Section Facts.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  (** Coverage of the task set, the curve class and the generator. *)
  Let cover_ts :=
    fma_forall_cover_sprop _ _ (@ArListRel Task) (@ar_list_to_imported Task) (@ar_list_to_rocq Task)
      (fma_list_source_total Task) (fma_list_target_total Task).
  Let cover_ma :=
    fma_forall_cover_sprop _ _ (CvMaxArrivalsRel Task)
      (fun cR => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT
        (fun tsk => cv_import_fun (cR tsk)))
      (fun cL => (fun tsk => cv_export_fun
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk))
        : prosa.model.task.arrival.curves.MaxArrivals Task)
      (CurvesCorrespondence.MaxArrivals_source_total Task)
      (CurvesCorrespondence.MaxArrivals_target_total Task).
  Let cover_gen :=
    fma_forall_cover_sprop _ _ (MsGeneratorRel Task Job)
      (fun gR => fun tsk nL tL => svc_list_to_imported
        (gR tsk (sub_nat_to_rocq nL) (sub_nat_to_rocq tL)))
      (fun gL => fun tsk n t => svc_list_to_rocq
        (gL tsk (sub_nat_to_imported n) (sub_nat_to_imported t)))
      (Generator_source_total Task Job) (Generator_target_total Task Job).

  Lemma fma_mem_task_related (tsk : Task) tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel (is_true (tsk \in tsR))
      (Lean.eq (ar_target_decide_mem Task tsk tsL) I.Bool_true).
  Proof.
    intro Hts. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
  Qed.

  Lemma fma_mem_task_transport (x y : Task) tsR tsL :
    Lean.eq x y -> ArListRel tsR tsL ->
    PropSPropRel (is_true (x \in tsR))
      (Lean.eq (ar_target_decide_mem Task y tsL) I.Bool_true).
  Proof.
    intros Hxy Hts. have E := imported_eq_to_coq_eq _ _ Hxy. destruct E.
    exact (fma_mem_task_related x _ _ Hts).
  Qed.

  Lemma fma_concrete_related cR cL (Hc : CvMaxArrivalsRel Task cR cL) gR gL
      (Hg : MsGeneratorRel Task Job gR gL) tsR tsL (Hts : ArListRel tsR tsL) :
    ArArrivalSequenceRel Job
      (@prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence
        Task Job cR gR tsR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence
        Task dT Job dJ cL gL tsL).
  Proof.
    intros tR tL Ht.
    exact (fma_svc_to_ar _ _ _ (concrete_arrival_sequence_correspondence Task Job cR cL Hc
      gR gL Hg tsR tsL tR tL (fma_ar_to_svc _ _ _ Hts) Ht)).
  Qed.

  (** *** Statements on the prefix construction (only the task type is fixed) *)

  Definition src_extend_horizon_size : Prop :=
    ltac:(body_of (fun s : S.statement_extend_horizon_size => s Task)).
  Definition tgt_extend_horizon_size : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_extend_horizon_size
      Task dT)).

  Theorem extend_horizon_size_correspondence :
    PropSPropRel src_extend_horizon_size tgt_extend_horizon_size.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply sub_nat_eq_correspondence; [|exact Ht].
    apply ms_size_related.
    exact (ms_lean_transport (fun m => SvcNatListRel _
      (I.Nat_repeat_inst1 (I.List_inst1 Lean.Nat)
        (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix Task dT cL tsk)
        m (I.List_nil_inst1 Lean.Nat))) _ _ Ht
      (ms_repeat_related _ _ (fun xsR xsL Hx =>
        extend_arrival_prefix_correspondence Task cR cL Hc tsk xsR xsL Hx) tR)).
  Qed.

  Definition src_prefix_up_to_size : Prop :=
    ltac:(body_of (fun s : S.statement_prefix_up_to_size => s Task)).
  Definition tgt_prefix_up_to_size : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_prefix_up_to_size
      Task dT)).

  Theorem prefix_up_to_size_correspondence :
    PropSPropRel src_prefix_up_to_size tgt_prefix_up_to_size.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply sub_nat_eq_correspondence.
    - exact (ms_size_related _ _ (maximal_arrival_prefix_correspondence Task cR cL Hc tsk tR tL Ht)).
    - exact (ms_succ_related tR tL Ht).
  Qed.

  Definition src_n_arrivals_at_prefix_inclusion1 : Prop :=
    ltac:(body_of (fun s : S.statement_n_arrivals_at_prefix_inclusion1 => s Task)).
  Definition tgt_n_arrivals_at_prefix_inclusion1 : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_n_arrivals_at_prefix_inclusion1 Task dT)).

  Theorem n_arrivals_at_prefix_inclusion1_correspondence :
    PropSPropRel src_n_arrivals_at_prefix_inclusion1 tgt_n_arrivals_at_prefix_inclusion1.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
    apply sub_nat_eq_correspondence.
    - exact (ms_nth_related _ _ _ _
        (maximal_arrival_prefix_correspondence Task cR cL Hc tsk hR hL Hh) Ht).
    - exact (ms_nth_related _ _ _ _
        (maximal_arrival_prefix_correspondence Task cR cL Hc tsk _ _
          (ms_succ_related hR hL Hh)) Ht).
  Qed.

  Definition src_n_arrivals_at_prefix_inclusion : Prop :=
    ltac:(body_of (fun s : S.statement_n_arrivals_at_prefix_inclusion => s Task)).
  Definition tgt_n_arrivals_at_prefix_inclusion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_n_arrivals_at_prefix_inclusion Task dT)).

  Theorem n_arrivals_at_prefix_inclusion_correspondence :
    PropSPropRel src_n_arrivals_at_prefix_inclusion tgt_n_arrivals_at_prefix_inclusion.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros h1R h1L Hh1.
    apply ar_forall_nat_correspondence. intros h2R h2L Hh2.
    apply ar_imp_correspondence.
    { exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ Ht Hh1) (ar_decide_le_related _ _ _ _ Hh1 Hh2))). }
    apply sub_nat_eq_correspondence.
    - exact (ms_nth_related _ _ _ _
        (maximal_arrival_prefix_correspondence Task cR cL Hc tsk h1R h1L Hh1) Ht).
    - exact (ms_nth_related _ _ _ _
        (maximal_arrival_prefix_correspondence Task cR cL Hc tsk h2R h2L Hh2) Ht).
  Qed.

  Definition src_max_arrivals_at_next_max_arrivals_eq : Prop :=
    ltac:(body_of (fun s : S.statement_max_arrivals_at_next_max_arrivals_eq => s Task)).
  Definition tgt_max_arrivals_at_next_max_arrivals_eq : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_max_arrivals_at_next_max_arrivals_eq
        Task dT)).

  Theorem max_arrivals_at_next_max_arrivals_eq_correspondence :
    PropSPropRel src_max_arrivals_at_next_max_arrivals_eq tgt_max_arrivals_at_next_max_arrivals_eq.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ht)|].
    rewrite -subn1.
    apply sub_nat_eq_correspondence.
    - exact (max_arrivals_at_correspondence Task cR cL Hc tsk tR tL Ht).
    - exact (next_max_arrival_correspondence Task cR cL Hc tsk _ _
        (maximal_arrival_prefix_correspondence Task cR cL Hc tsk _ _
          (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical (S O))))).
  Qed.

  Definition src_n_arrivals_at_leq : Prop :=
    ltac:(body_of (fun s : S.statement_n_arrivals_at_leq => s Task)).
  Definition tgt_n_arrivals_at_leq : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_n_arrivals_at_leq
      Task dT)).

  Theorem n_arrivals_at_leq_correspondence :
    PropSPropRel src_n_arrivals_at_leq tgt_n_arrivals_at_leq.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hc)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hd Ht)|].
    apply sub_nat_le_correspondence.
    - exact (max_arrivals_at_correspondence Task cR cL Hc tsk tR tL Ht).
    - apply svc_target_sub_related.
      + exact (Hc tsk _ _ (ms_succ_related dR dL Hd)).
      + exact (ms_interval_sum_related _ _ _ _ _ _
          (svc_target_sub_related _ _ _ _ Ht Hd) Ht
          (fun xR xL Hx => max_arrivals_at_correspondence Task cR cL Hc tsk xR xL Hx)).
  Qed.

  (** *** Statements on the concrete arrival sequence *)

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job jcR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ jcL j).

  Lemma fma_generator_valid_related gR gL (Hg : MsGeneratorRel Task Job gR gL) :
    PropSPropRel
      (forall (tsk : Task) (n : nat) (t : nat) (j : Job),
        is_true (j \in gR tsk n t) ->
        @prosa.model.task.concept.job_task Job Task jtR j = tsk /\
        @prosa.behavior.job.job_arrival Job jaR j = t /\
        is_true (leq (@prosa.behavior.job.job_cost Job jcR j)
          (@prosa.model.task.concept.task_cost Task tcR tsk)))
      (forall (tsk : Task) (nL tL : Lean.Nat) (j : Job),
        Lean.eq (ar_target_decide_mem Job j (gL tsk nL tL)) I.Bool_true ->
        And (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk)
          (And (Lean.eq (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j) tL)
            (ar_target_le (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ jcL j)
              (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk)))).
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    { exact (ar_bool_truth_correspondence _ _
        (ar_decide_mem_related Job j _ _ (fma_svc_to_ar _ _ _ (Hg tsk _ _ _ _ Hn Ht)))). }
    apply ar_and_correspondence;
      [exact (fma_eq_correspondence _ _ _ _ _ (Hjt j) (@Lean.eq_refl _ tsk))|].
    apply ar_and_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) Ht)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hjc j) (Htc tsk)).
  Qed.

  Lemma fma_generator_size_related gR gL (Hg : MsGeneratorRel Task Job gR gL) tsR tsL
      (Hts : ArListRel tsR tsL) :
    PropSPropRel
      (forall (tsk : Task) (n : nat) (t : nat), is_true (tsk \in tsR) -> size (gR tsk n t) = n)
      (forall (tsk : Task) (nL tL : Lean.Nat),
        Lean.eq (ar_target_decide_mem Task tsk tsL) I.Bool_true ->
        Lean.eq (I.List_length Job (gL tsk nL tL)) nL).
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    exact (sub_nat_eq_correspondence _ _ _ _
      (ari_size_related Job _ _ (fma_svc_to_ar _ _ _ (Hg tsk _ _ _ _ Hn Ht))) Hn).
  Qed.

  Definition src_arr_seq_is_a_set : Prop :=
    ltac:(body_of (fun s : S.statement_arr_seq_is_a_set => s Task Job)).
  Definition tgt_arr_seq_is_a_set : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_arr_seq_is_a_set
      Task dT Job dJ)).

  Theorem arr_seq_is_a_set_correspondence :
    PropSPropRel src_arr_seq_is_a_set tgt_arr_seq_is_a_set.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence.
    { apply ar_forall_nat_correspondence. intros t1R t1L H1.
      apply ar_forall_nat_correspondence. intros t2R t2L H2.
      exact (ar_uniq_correspondence Job _ _
        (arrivals_between_correspondence_certificate Job _ _ Harr _ _ _ _ H1 H2)). }
    exact (arrival_sequence_uniq_correspondence_certificate Job _ _ Harr).
  Qed.

  Definition src_concrete_all_jobs_from_taskset : Prop :=
    ltac:(body_of (fun s : S.statement_concrete_all_jobs_from_taskset =>
      s Task tcR Job jtR jaR jcR)).
  Definition tgt_concrete_all_jobs_from_taskset : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_concrete_all_jobs_from_taskset
        Task dT tcL Job dJ jtL jaL jcL)).

  Theorem concrete_all_jobs_from_taskset_correspondence :
    PropSPropRel src_concrete_all_jobs_from_taskset tgt_concrete_all_jobs_from_taskset.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job _ _ j Harr)|].
    exact (fma_mem_task_transport _ _ _ _ (Hjt j) Hts).
  Qed.

  Definition src_arrival_times_are_consistent : Prop :=
    ltac:(body_of (fun s : S.statement_arrival_times_are_consistent =>
      s Task tcR Job jtR jaR jcR)).
  Definition tgt_arrival_times_are_consistent : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_arrival_times_are_consistent
        Task dT tcL Job dJ jtL jaL jcL)).

  Theorem arrival_times_are_consistent_correspondence :
    PropSPropRel src_arrival_times_are_consistent tgt_arrival_times_are_consistent.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    exact (consistent_arrival_times_correspondence_certificate Job _ _ _ _ Hja Harr).
  Qed.

  Definition src_concrete_valid_job_cost : Prop :=
    ltac:(body_of (fun s : S.statement_concrete_valid_job_cost =>
      s Task tcR Job jtR jaR jcR)).
  Definition tgt_concrete_valid_job_cost : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_concrete_valid_job_cost
        Task dT tcL Job dJ jtL jaL jcL)).

  Theorem concrete_valid_job_cost_correspondence :
    PropSPropRel src_concrete_valid_job_cost tgt_concrete_valid_job_cost.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job _ _ j Harr)|].
    unfold prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
    exact (ar_bool_truth_correspondence _ _
      (ar_decide_le_related _ _ _ _ (Hjc j)
        (sub_imported_eq_trans _ _ _ (Htc _)
          (sub_imported_eq_congr (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL)
            _ _ (Hjt j))))).
  Qed.

  Definition src_task_arrivals_at_eq_generate_jobs_at : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_at_eq_generate_jobs_at =>
      s Task tcR Job jtR jaR jcR)).
  Definition tgt_task_arrivals_at_eq_generate_jobs_at : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_task_arrivals_at_eq_generate_jobs_at
        Task dT tcL Job dJ jtL jaL jcL)).

  Theorem task_arrivals_at_eq_generate_jobs_at_correspondence :
    PropSPropRel src_task_arrivals_at_eq_generate_jobs_at
      tgt_task_arrivals_at_eq_generate_jobs_at.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (ar_list_eq_correspondence Job _ _ _ _
      (task_arrivals_at_correspondence Job Task jtR jtL Hjt _ _ Harr tsk tsk tR tL
        (@Lean.eq_refl _ _) Ht)
      (fma_svc_to_ar _ _ _ (Hg tsk _ _ _ _
        (max_arrivals_at_correspondence Task cR cL Hc tsk tR tL Ht) Ht))).
  Qed.

  Definition src_task_arrivals_at_eq : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_at_eq => s Task tcR Job jtR jaR jcR)).
  Definition tgt_task_arrivals_at_eq : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_task_arrivals_at_eq
      Task dT tcL Job dJ jtL jaL jcL)).

  Theorem task_arrivals_at_eq_correspondence :
    PropSPropRel src_task_arrivals_at_eq tgt_task_arrivals_at_eq.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_size_related gR gL Hg tsR tsL Hts)|].
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (sub_nat_eq_correspondence _ _ _ _
      (ari_size_related Job _ _ (task_arrivals_at_correspondence Job Task jtR jtL Hjt _ _ Harr
        tsk tsk tR tL (@Lean.eq_refl _ _) Ht))
      (max_arrivals_at_correspondence Task cR cL Hc tsk tR tL Ht)).
  Qed.

  Definition src_number_of_task_arrivals_eq : Prop :=
    ltac:(body_of (fun s : S.statement_number_of_task_arrivals_eq =>
      s Task tcR Job jtR jaR jcR)).
  Definition tgt_number_of_task_arrivals_eq : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_number_of_task_arrivals_eq
        Task dT tcL Job dJ jtL jaL jcL)).

  Theorem number_of_task_arrivals_eq_correspondence :
    PropSPropRel src_number_of_task_arrivals_eq tgt_number_of_task_arrivals_eq.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_size_related gR gL Hg tsR tsL Hts)|].
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fma_mem_task_related tsk _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    exact (sub_nat_eq_correspondence _ _ _ _
      (number_of_task_arrivals_correspondence Job Task jtR jtL Hjt _ _ Harr tsk tsk
        t1R t1L t2R t2L (@Lean.eq_refl _ _) H1 H2)
      (ms_interval_sum_related _ _ _ _ _ _ H1 H2
        (fun xR xL Hx => max_arrivals_at_correspondence Task cR cL Hc tsk xR xL Hx))).
  Qed.

  Definition src_concrete_is_arrival_curve : Prop :=
    ltac:(body_of (fun s : S.statement_concrete_is_arrival_curve =>
      s Task tcR Job jtR jaR jcR)).
  Definition tgt_concrete_is_arrival_curve : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Implementation_Facts_MaximalArrivalSequence_concrete_is_arrival_curve
        Task dT tcL Job dJ jtL jaL jcL)).

  Theorem concrete_is_arrival_curve_correspondence :
    PropSPropRel src_concrete_is_arrival_curve tgt_concrete_is_arrival_curve.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply cover_ma. intros cR cL Hc.
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hc)|].
    apply cover_gen. intros gR gL Hg.
    have Harr := fma_concrete_related cR cL Hc gR gL Hg tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fma_generator_size_related gR gL Hg tsR tsL Hts)|].
    apply ar_imp_correspondence; [exact (fma_generator_valid_related gR gL Hg)|].
    exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt _ _ Harr
      tsR tsL Hts cR cL Hc).
  Qed.
End Facts.
