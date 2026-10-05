From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop order.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import FactsElfAthepBoundSemanticSource.
From prosa Require Import util.int model.priority.gel model.priority.elf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsElfAthepBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers PriorityElfHelpers ElfAthepBoundCorrespondence.

Module I := ImportedFactsElfAthepBound.
Module S := FactsElfAthepBoundSemanticSource.FactsElfAthepBoundSemanticSource.

Import GRing.Theory Num.Theory.

(** Statement correspondences for [analysis/facts/workload/elf_athep_bound.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, [task_cost], a leading
    [MaxArrivals] instance, priority points, [job_task], [job_arrival],
    [job_cost], a leading processor state, a leading arrival sequence);
    target side: the imported Lean theorem types at related inputs
    ([SubNatRel] on [task_cost], the accepted [CvMaxArrivalsRel], the
    accepted [GelPriorityPointRel], [Lean.eq] on [job_task],
    [ArJobArrivalRel], [SvcJobCostRel], the accepted two-sided
    [SvcProcessorStateRel], [ArArrivalSequenceRel]).  Binders quantified
    inside the statements are covered in both directions: task sets through
    the list conversion, schedules through the processor-state conversion,
    FP policies pointwise on Booleans (the accepted [pco_forall_fp]), Nats;
    tasks and jobs are identity carriers.  The ELF policy is the accepted
    [ELF_correspondence]; the ELF workload-bound definitions (including the
    integer interval length, [`|Num.max 0 _|] and integer subtraction) are
    the accepted definition certificate; [delta%:R] and [t1%:R + _] on
    [int] are the accepted GEL cast/addition relations; workloads,
    arrivals, the request-bound function and the workload-bound predicate
    are closed by the accepted certificates re-instantiated at this
    artifact (as in the accepted EDF workload-bound facts certificate).  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma felab_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma felab_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma felab_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma felab_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

(** [n%:R] on [int] against Lean's [Nat.cast], through the accepted exported cast equation. *)
Lemma felab_cast_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> GelIntRel (nR%:R : int) (I.Nat_cast_inst1 I.Int I.instNatCastInt nL).
Proof.
  intro Hn. rewrite natz. unfold GelIntRel. cbn [gel_int_to_imported].
  exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_congr I.Int_ofNat _ _ Hn)
    (sub_imported_eq_sym _ _ (P_cast nL))).
Qed.

Section FpDerived.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Lemma felab_ep_task_related (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task. cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp x y) (Hfp y x)).
  Qed.

  Lemma felab_hp_task_related (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.hp_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.hp_task. cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp x y) (pd_bool_not_related _ _ (Hfp y x))).
  Qed.
End FpDerived.

Section Facts.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  (** *** The ELF policy and the per-task higher-or-equal-priority predicate *)

  Lemma felab_elf_related fR fL (Hf : PdFPRel Task fR fL) (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job (@prosa.model.priority.elf.ELF Task ppR Job jaR jtR fR) x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ
        (I.Prosa_Model_Priority_Elf_ELF Task dT ppL Job dJ jaL jtL fL) x y).
  Proof. exact (ELF_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt fR fL Hf x y). Qed.

  Lemma felab_job_task_eq_related (jo : Job) (tsk : Task) :
    ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR jo == tsk)
      (I.Decidable_decide
        (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk)
        (dT (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk)).
  Proof.
    refine (felab_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR jo == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt jo) _).
    exact (felab_decide_eq_related Task _ tsk).
  Qed.

  Lemma felab_hep_from_related fR fL (Hf : PdFPRel Task fR fL) (j : Job) (tsk_o : Task) :
    ArPredRel (fun jo => @prosa.model.priority.definitions.hep_job Job
        (@prosa.model.priority.elf.ELF Task ppR Job jaR jtR fR) jo j
        && (@prosa.model.task.concept.job_task Job Task jtR jo == tsk_o))
      (fun jo => I.Bool_and (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ
          (I.Prosa_Model_Priority_Elf_ELF Task dT ppL Job dJ jaL jtL fL) jo j)
        (I.Decidable_decide
          (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk_o)
          (dT (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk_o))).
  Proof.
    intro jo.
    exact (ar_bool_and_related _ _ _ _ (felab_elf_related fR fL Hf jo j) (felab_job_task_eq_related jo tsk_o)).
  Qed.

  Let HEP_WL fR fL Hf j tsk_o t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :=
    workload_of_jobs_correspondence Job costR costL Hcost _ _ (felab_hep_from_related fR fL Hf j tsk_o) _ _
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2).

  (** *** Task-concept and job predicates *)

  Lemma felab_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    exact (felab_job_task_eq_related j tsk).
  Qed.

  Lemma felab_job_cost_positive_related (j : Job) :
    PropSPropRel (is_true (@prosa.model.job.properties.job_cost_positive Job costR j))
      (Lean.eq (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j) I.Bool_true).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))).
  Qed.

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  (** *** Covers *)

  Lemma felab_list_to_target_rel (xs : seq Task) : ArListRel xs (ar_list_to_imported xs).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Lemma felab_list_to_source_rel (xs : I.List Task) : ArListRel (ar_list_to_rocq xs) xs.
  Proof. exact (ar_list_target_roundtrip xs). Qed.

  Let cover_ts :=
    felab_forall_cover_sprop _ _ (@ArListRel Task)
      ar_list_to_imported ar_list_to_rocq felab_list_to_target_rel felab_list_to_source_rel.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  (** *** total_ep_tsk_workload_shorten_range *)

  Definition src_total_ep_tsk_workload_shorten_range : Prop :=
    ltac:(body_of (fun s : S.statement_total_ep_tsk_workload_shorten_range => s Task ppR Job jtR jaR costR arrR)).
  Definition tgt_total_ep_tsk_workload_shorten_range : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Workload_ElfAthepBound_total_ep_tsk_workload_shorten_range
      Task dT ppL Job dJ jtL jaL costL arrL)).
  Theorem total_ep_tsk_workload_shorten_range_correspondence :
    PropSPropRel src_total_ep_tsk_workload_shorten_range tgt_total_ep_tsk_workload_shorten_range.
  Proof.
    imp VALID.
    apply ar_forall_identity_correspondence. intro tsk.
    apply (pco_forall_fp Task). intros fR fL Hf.
    apply ar_forall_identity_correspondence. intro j.
    imp (ar_bool_truth_correspondence _ _ (felab_job_of_task_related tsk j)).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_forall_identity_correspondence. intro tsk_o.
    have HA := svc_target_sub_related _ _ _ _ (Hja j) Ht1.
    have HL := ep_task_interfering_interval_length_correspondence Task ppR ppL Hpp tsk tsk_o _ _ HA.
    imp (ar_bool_truth_correspondence _ _ (gel_le_related _ _ _ _ HL (felab_cast_related _ _ Hd))).
    imp (ar_bool_truth_correspondence _ _ (felab_ep_task_related Task fR fL Hf tsk tsk_o)).
    exact (sub_nat_le_correspondence _ _ _ _
      (HEP_WL fR fL Hf j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd))
      (HEP_WL fR fL Hf j tsk_o _ _ Ht1 _ _
        (eab_absmax_related _ _ (gel_add_related _ _ _ _ Ht1 HL)))).
  Qed.

  (** *** sum_of_hep_workloads_partitioned *)

  Definition src_sum_of_hep_workloads_partitioned : Prop :=
    ltac:(body_of (fun s : S.statement_sum_of_hep_workloads_partitioned => s Task ppR Job jtR jaR costR arrR)).
  Definition tgt_sum_of_hep_workloads_partitioned : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Workload_ElfAthepBound_sum_of_hep_workloads_partitioned
      Task dT ppL Job dJ jtL jaL costL arrL)).
  Theorem sum_of_hep_workloads_partitioned_correspondence :
    PropSPropRel src_sum_of_hep_workloads_partitioned tgt_sum_of_hep_workloads_partitioned.
  Proof.
    apply cover_ts. intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro tsk.
    apply (pco_forall_fp Task). intros fR fL Hf.
    apply ar_forall_identity_correspondence. intro j.
    imp (ar_bool_truth_correspondence _ _ (felab_job_of_task_related tsk j)).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have W := fun tsk_o => HEP_WL fR fL Hf j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd).
    exact (sub_nat_eq_correspondence _ _ _ _
      (rbf_sum_filtered_related Task _ _ W _ _ (fun tsk_o => rbf_neq_related Task tsk_o tsk) _ _ Hts)
      (svc_target_add_related _ _ _ _
        (rbf_sum_filtered_related Task _ _ W _ _
          (fun tsk_o => ar_bool_and_related _ _ _ _ (felab_ep_task_related Task fR fL Hf tsk tsk_o)
            (rbf_neq_related Task tsk_o tsk)) _ _ Hts)
        (rbf_sum_filtered_related Task _ _ W _ _
          (fun tsk_o => felab_hp_task_related Task fR fL Hf tsk_o tsk) _ _ Hts))).
  Qed.

  Section MA.
    Variable tcR : prosa.model.task.concept.TaskCost Task.
    Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
    Hypothesis Htc : forall tsk : Task,
      SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
    Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
    Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
    Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

    Lemma felab_task_cost_of_job_related (j : Job) :
      SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
          (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
    Proof.
      exact (felab_lean_transport
        (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
          (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
    Qed.

    Lemma felab_valid_job_costs_related :
      PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
        (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
    Proof.
      unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
      cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      unfold prosa.model.task.concept.valid_job_cost.
      cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
      exact (ar_bool_truth_correspondence _ _
        (svc_decide_le_related _ _ _ _ (Hcost j) (felab_task_cost_of_job_related j))).
    Qed.

    Lemma felab_all_jobs_from_taskset_related tsR tsL (Hts : ArListRel tsR tsL) :
      PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
        (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
    Proof.
      unfold prosa.model.task.concept.all_jobs_from_taskset.
      cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
      exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
    Qed.

    Let RESPS tsR tsL Hts :=
      taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
        maR maL Hma.

    (** **** sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload *)

    Definition src_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload : Prop :=
      ltac:(body_of (fun s : S.statement_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload =>
        s Task tcR maR ppR Job jtR jaR costR arrR)).
    Definition tgt_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Workload_ElfAthepBound_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload
          Task dT tcL maL ppL Job dJ jtL jaL costL arrL)).
    Theorem sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload_correspondence :
      PropSPropRel src_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload
        tgt_sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload.
    Proof.
      imp VALID.
      imp felab_valid_job_costs_related.
      apply cover_ts. intros tsR tsL Hts.
      imp (RESPS tsR tsL Hts).
      apply ar_forall_identity_correspondence. intro tsk.
      apply (pco_forall_fp Task). intros fR fL Hf.
      apply ar_forall_identity_correspondence. intro j.
      imp (ar_bool_truth_correspondence _ _ (felab_job_of_task_related tsk j)).
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      imp (sub_nat_lt_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ Ht1 Hd) Ht2).
      exact (sub_nat_le_correspondence _ _ _ _
        (rbf_sum_filtered_related Task _ _
          (fun tsk_o => HEP_WL fR fL Hf j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd))
          _ _ (fun tsk_o => ar_bool_and_related _ _ _ _ (felab_ep_task_related Task fR fL Hf tsk tsk_o)
            (rbf_neq_related Task tsk_o tsk)) _ _ Hts)
        (bound_on_ep_task_workload_correspondence Task tcR tcL Htc maR maL Hma ppR ppL Hpp tsR tsL Hts
          fR fL Hf tsk _ _ _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1) Hd)).
    Qed.

    (** **** sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload *)

    Definition src_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload : Prop :=
      ltac:(body_of (fun s : S.statement_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload =>
        s Task tcR maR ppR Job jtR jaR costR arrR)).
    Definition tgt_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Workload_ElfAthepBound_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload
          Task dT tcL maL ppL Job dJ jtL jaL costL arrL)).
    Theorem sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload_correspondence :
      PropSPropRel src_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload
        tgt_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload.
    Proof.
      imp felab_valid_job_costs_related.
      apply cover_ts. intros tsR tsL Hts.
      imp (RESPS tsR tsL Hts).
      apply ar_forall_identity_correspondence. intro tsk.
      apply (pco_forall_fp Task). intros fR fL Hf.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      exact (sub_nat_le_correspondence _ _ _ _
        (rbf_sum_filtered_related Task _ _
          (fun tsk_o => HEP_WL fR fL Hf j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd))
          _ _ (fun tsk_o => felab_hp_task_related Task fR fL Hf tsk_o tsk) _ _ Hts)
        (bound_on_hp_task_workload_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
          fR fL Hf tsk _ _ Hd)).
    Qed.

    (** **** sum_of_workloads_is_at_most_bound_on_total_hep_workload *)

    Definition src_sum_of_workloads_is_at_most_bound_on_total_hep_workload : Prop :=
      ltac:(body_of (fun s : S.statement_sum_of_workloads_is_at_most_bound_on_total_hep_workload =>
        s Task tcR maR ppR Job jtR jaR costR arrR)).
    Definition tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Workload_ElfAthepBound_sum_of_workloads_is_at_most_bound_on_total_hep_workload
          Task dT tcL maL ppL Job dJ jtL jaL costL arrL)).
    Theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence :
      PropSPropRel src_sum_of_workloads_is_at_most_bound_on_total_hep_workload
        tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload.
    Proof.
      imp VALID.
      imp felab_valid_job_costs_related.
      apply cover_ts. intros tsR tsL Hts.
      imp (RESPS tsR tsL Hts).
      apply ar_forall_identity_correspondence. intro tsk.
      apply (pco_forall_fp Task). intros fR fL Hf.
      apply ar_forall_identity_correspondence. intro j.
      imp (ar_bool_truth_correspondence _ _ (felab_job_of_task_related tsk j)).
      imp (felab_job_cost_positive_related j).
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      imp (sub_nat_lt_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ Ht1 Hd) Ht2).
      exact (sub_nat_le_correspondence _ _ _ _
        (rbf_sum_filtered_related Task _ _
          (fun tsk_o => HEP_WL fR fL Hf j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd))
          _ _ (fun tsk_o => rbf_neq_related Task tsk_o tsk) _ _ Hts)
        (bound_on_athep_workload_correspondence Task tcR tcL Htc maR maL Hma ppR ppL Hpp tsR tsL Hts
          fR fL Hf tsk _ _ _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1) Hd)).
    Qed.

    (** **** bound_on_athep_workload_is_valid *)

    Section Sched.
      Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
      Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
      Variable R : SvcProcessorStateRel Job PStateR PStateL.

      Definition felab_sched_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
          I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
        fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

      Definition felab_sched_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
          @prosa.behavior.schedule.schedule Job PStateR :=
        fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

      Lemma felab_sched_to_target_rel schedR :
        SvcScheduleRel Job PStateR PStateL R schedR (felab_sched_to_target schedR).
      Proof.
        intros tR tL Ht. unfold felab_sched_to_target.
        rewrite (felab_nat_input _ _ Ht).
        exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
      Qed.

      Lemma felab_sched_to_source_rel schedL :
        SvcScheduleRel Job PStateR PStateL R (felab_sched_to_source schedL) schedL.
      Proof.
        intros tR tL Ht. unfold felab_sched_to_source.
        exact (felab_lean_transport
          (fun x => svc_ps_state_rel Job PStateR PStateL R
            (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR))) (schedL x))
          _ _ Ht (svc_ps_state_rel_surjective Job PStateR PStateL R _)).
      Qed.

      Let cover_sched :=
        felab_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
          felab_sched_to_target felab_sched_to_source felab_sched_to_target_rel felab_sched_to_source_rel.

      Definition src_bound_on_athep_workload_is_valid : Prop :=
        ltac:(body_of (fun s : S.statement_bound_on_athep_workload_is_valid =>
          s Task tcR maR ppR Job jtR jaR costR PStateR arrR)).
      Definition tgt_bound_on_athep_workload_is_valid : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Workload_ElfAthepBound_bound_on_athep_workload_is_valid
          Task dT tcL maL ppL Job dJ jtL jaL costL PStateL arrL)).
      Theorem bound_on_athep_workload_is_valid_correspondence :
        PropSPropRel src_bound_on_athep_workload_is_valid tgt_bound_on_athep_workload_is_valid.
      Proof.
        imp VALID.
        imp felab_valid_job_costs_related.
        apply cover_ts. intros tsR tsL Hts.
        imp (felab_all_jobs_from_taskset_related tsR tsL Hts).
        imp (RESPS tsR tsL Hts).
        apply ar_forall_identity_correspondence. intro tsk.
        apply cover_sched. intros schedR schedL Hsched.
        apply (pco_forall_fp Task). intros fR fL Hf.
        exact (athep_workload_is_bounded_correspondence Task Job costR costL Hcost jaR jaL Hja
          jtR jtL Hjt PStateR PStateL R _ _ (felab_elf_related fR fL Hf) arrR arrL Harr
          schedR schedL Hsched tsk _ _
          (fun aR aL dR dL Ha Hd => bound_on_athep_workload_correspondence Task tcR tcL Htc maR maL Hma
            ppR ppL Hpp tsR tsL Hts fR fL Hf tsk aR dR aL dL Ha Hd)).
      Qed.
    End Sched.
  End MA.
End Facts.
