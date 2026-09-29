From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop order.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import ElfAthepBoundSemanticSource.
From prosa Require Import util.int model.priority.gel model.priority.elf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsElfFloatingNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  RequestBoundFunctionCorrespondence EdfAthepBoundCorrespondence
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers.

Module I := ImportedRtaRsElfFloatingNonpreemptive.
Module S := ElfAthepBoundSemanticSource.ElfAthepBoundSemanticSource.

Import GRing.Theory Num.Theory Order.TTheory.

(** Definition certificate for [analysis/definitions/workload/elf_athep_bound.v].

    Source side: the extracted byte-identical definition block (its
    request-bound-function import bound to the accepted extracted RBF
    source); target side: the compiled Lean definitions.  Inputs:
    [TaskCost] and [MaxArrivals] pointwise by [SubNatRel], priority points
    by the accepted [GelPriorityPointRel], the FP policy pointwise on
    Booleans ([PdFPRel]), task sets by [ArListRel], the Nat arguments by
    [SubNatRel]; the integer result by the accepted constructor-wise
    [GelIntRel].  The RBFs, the filtered sequence sums and [!=] are the
    accepted [RequestBoundFunctionCorrespondence]; [minn] is the accepted
    EDF workload-bound relation to Lean's [min]; [n%:R + z] is the accepted
    GEL relation.  Integer subtraction and [`|Num.max 0 z|] are related
    constructor-wise: MathComp facts on [Posz]/[Negz] on the source side,
    kernel-checked Lean constructor equations exported with the artifact on
    the target side.  No source or target theorem is used. *)

Notation P_sub_oo_le := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_ofNat_ofNat_le.
Notation P_sub_oo_gt := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_ofNat_ofNat_gt.
Notation P_sub_on := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_ofNat_negSucc.
Notation P_sub_no := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_negSucc_ofNat.
Notation P_sub_nn_le := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_negSucc_negSucc_le.
Notation P_sub_nn_gt := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_negSucc_negSucc_gt.
Notation P_abs_o := I.Prosa_Validation_ElfAthepBoundInterface_production_int_natAbs_max_ofNat.
Notation P_abs_n := I.Prosa_Validation_ElfAthepBoundInterface_production_int_natAbs_max_negSucc.

(** ** Target operations, read off the exported equations *)

Definition eab_target_sub (x y : I.Int) : I.Int :=
  ltac:(let T := type of (P_sub_on (sub_nat_to_imported 0) (sub_nat_to_imported 0)) in
        match T with @Lean.eq _ (?f (I.Int_ofNat _) (I.Int_negSucc _)) _ => exact (f x y) end).

Definition eab_target_absmax (z : I.Int) : Lean.Nat :=
  ltac:(let T := type of (P_abs_o (sub_nat_to_imported 0)) in
        match T with @Lean.eq _ (?g (?h (I.Int_ofNat _))) _ => exact (g (h z)) end).

(** ** Source facts on MathComp integers *)

Lemma eab_subz_pp_le (m n : nat) : (n <= m)%N -> (Posz m - Posz n)%R = Posz (m - n).
Proof. by move=> h; rewrite subzn. Qed.

Lemma eab_subz_pp_gt (m n : nat) : ~~ (n <= m)%N -> (Posz m - Posz n)%R = Negz (n - m - 1).
Proof.
  rewrite -ltnNge => h. rewrite NegzE subn1 prednK ?subn_gt0 //.
  by rewrite -subzn ?opprB // ltnW.
Qed.

Lemma eab_subz_pn (m n : nat) : (Posz m - Negz n)%R = Posz (m + n + 1).
Proof. by rewrite NegzE opprK -!PoszD addn1 addnS. Qed.

Lemma eab_subz_np (m n : nat) : (Negz m - Posz n)%R = Negz (m + n).
Proof. by rewrite !NegzE -opprD -PoszD addSn. Qed.

Lemma eab_subz_nn_le (m n : nat) : (m <= n)%N -> (Negz m - Negz n)%R = Posz (n - m).
Proof. by move=> h; rewrite !NegzE opprK addrC subzn. Qed.

Lemma eab_subz_nn_gt (m n : nat) : ~~ (m <= n)%N -> (Negz m - Negz n)%R = Negz (m - n - 1).
Proof.
  rewrite -ltnNge => h. rewrite !NegzE opprK subn1 prednK ?subn_gt0 //.
  rewrite -subzn ?(ltnW h) // opprB addrC -(addn1 n) -(addn1 m) !PoszD opprD addrACA subrr addr0.
  by [].
Qed.

Lemma eab_absmax_p (n : nat) : `|Num.max 0%R (Posz n)| = n.
Proof. by rewrite max_r. Qed.

Lemma eab_absmax_n (n : nat) : `|Num.max 0%R (Negz n)| = 0%N.
Proof. by rewrite max_l. Qed.

(** ** Nat helpers *)

Lemma eab_sub1_related (a b : nat) :
  SubNatRel (a - b - 1) (nat_target_sub (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported 1)).
Proof.
  exact (nat_target_sub_correspondence _ _ _ _
    (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
    (sub_nat_rel_canonical 1)).
Qed.

Lemma eab_add1_related (a b : nat) :
  SubNatRel (a + b + 1) (nat_target_add (nat_target_add (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported 1)).
Proof.
  exact (nat_target_add_correspondence _ _ _ _
    (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
    (sub_nat_rel_canonical 1)).
Qed.

(** ** Integer subtraction *)

Lemma eab_sub_canonical (x y : int) :
  GelIntRel (x - y)%R (eab_target_sub (gel_int_to_imported x) (gel_int_to_imported y)).
Proof.
  unfold GelIntRel, eab_target_sub.
  destruct x as [m|m], y as [n|n]; cbn [gel_int_to_imported].
  - have Hle := sub_nat_le_correspondence n (sub_nat_to_imported n) m (sub_nat_to_imported m)
      (sub_nat_rel_canonical n) (sub_nat_rel_canonical m).
    destruct (leq n m) eqn:E.
    + rewrite (eab_subz_pp_le m n E). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_oo_le _ _ (prop_to_sprop _ _ Hle isT)))).
      exact (sub_imported_eq_congr I.Int_ofNat _ _
        (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))).
    + rewrite (eab_subz_pp_gt m n (negbT E)). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_oo_gt _ _ (fun H => gel_coq_false_to_target
          (Bool.diff_false_true (sprop_to_prop _ _ Hle H)))))).
      exact (sub_imported_eq_congr I.Int_negSucc _ _ (eab_sub1_related n m)).
  - rewrite eab_subz_pn. cbn [gel_int_to_imported].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_sub_on _ _))).
    exact (sub_imported_eq_congr I.Int_ofNat _ _ (eab_add1_related m n)).
  - rewrite eab_subz_np. cbn [gel_int_to_imported].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_sub_no _ _))).
    exact (sub_imported_eq_congr I.Int_negSucc _ _
      (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))).
  - have Hle := sub_nat_le_correspondence m (sub_nat_to_imported m) n (sub_nat_to_imported n)
      (sub_nat_rel_canonical m) (sub_nat_rel_canonical n).
    destruct (leq m n) eqn:E.
    + rewrite (eab_subz_nn_le m n E). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_nn_le _ _ (prop_to_sprop _ _ Hle isT)))).
      exact (sub_imported_eq_congr I.Int_ofNat _ _
        (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical n) (sub_nat_rel_canonical m))).
    + rewrite (eab_subz_nn_gt m n (negbT E)). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_nn_gt _ _ (fun H => gel_coq_false_to_target
          (Bool.diff_false_true (sprop_to_prop _ _ Hle H)))))).
      exact (sub_imported_eq_congr I.Int_negSucc _ _ (eab_sub1_related m n)).
Qed.

Lemma eab_sub_related xR xL yR yL :
  GelIntRel xR xL -> GelIntRel yR yL -> GelIntRel (xR - yR)%R (eab_target_sub xL yL).
Proof.
  intros Hx Hy. unfold GelIntRel.
  exact (sub_imported_eq_trans _ _ _ (eab_sub_canonical xR yR)
    (sub_imported_eq_congr2 eab_target_sub _ _ _ _ Hx Hy)).
Qed.

(** ** [`|Num.max 0 z|] *)

Lemma eab_absmax_canonical (z : int) :
  SubNatRel `|Num.max 0%R z| (eab_target_absmax (gel_int_to_imported z)).
Proof.
  unfold eab_target_absmax.
  destruct z as [n|n]; cbn [gel_int_to_imported].
  - rewrite eab_absmax_p.
    exact (sub_imported_eq_trans _ _ _ (sub_nat_rel_canonical n) (sub_imported_eq_sym _ _ (P_abs_o _))).
  - rewrite eab_absmax_n.
    exact (sub_imported_eq_trans _ _ _ (sub_nat_rel_canonical 0) (sub_imported_eq_sym _ _ (P_abs_n _))).
Qed.

Lemma eab_absmax_related zR zL :
  GelIntRel zR zL -> SubNatRel `|Num.max 0%R zR| (eab_target_absmax zL).
Proof.
  intro Hz.
  exact (sub_imported_eq_trans _ _ _ (eab_absmax_canonical zR)
    (sub_imported_eq_congr eab_target_absmax _ _ Hz)).
Qed.

(** ** Definitions *)

Section ElfAthep.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Theorem ep_task_interfering_interval_length_correspondence (tsk tsk_o : Task)
      (AR : nat) (AL : Lean.Nat) (HA : SubNatRel AR AL) :
    GelIntRel (@S.ep_task_interfering_interval_length Task ppR tsk tsk_o AR)
      (I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length
        Task dT ppL tsk tsk_o AL).
  Proof.
    unfold S.ep_task_interfering_interval_length.
    cbn [I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length].
    exact (eab_sub_related _ _ _ _
      (gel_add_related _ _ _ _ (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical 1)) (Hpp tsk))
      (Hpp tsk_o)).
  Qed.

  Lemma eab_ep_task_related (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task. cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp x y) (Hfp y x)).
  Qed.

  Theorem bound_on_ep_task_workload_correspondence (tsk : Task) (aR dR : nat) (aL dL : Lean.Nat) :
    SubNatRel aR aL -> SubNatRel dR dL ->
    SubNatRel (@S.bound_on_ep_task_workload Task tcR maR ppR tsR fpR tsk aR dR)
      (I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_ep_task_workload
        Task dT tcL maL ppL tsL fpL tsk aL dL).
  Proof.
    intros Ha Hd. unfold S.bound_on_ep_task_workload. cbv zeta.
    cbn [I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_ep_task_workload].
    apply rbf_sum_filtered_related; [| |exact Hts].
    - intro o.
      exact (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma o _ _
        (eab_min_related _ _ _ _
          (eab_absmax_related _ _ (ep_task_interfering_interval_length_correspondence tsk o aR aL Ha))
          Hd)).
    - intro o. exact (ar_bool_and_related _ _ _ _ (eab_ep_task_related tsk o) (rbf_neq_related Task o tsk)).
  Qed.

  Theorem bound_on_hp_task_workload_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.bound_on_hp_task_workload Task tcR maR tsR fpR tsk dR)
      (I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload
        Task dT tcL maL tsL fpL tsk dL).
  Proof.
    intro Hd. unfold S.bound_on_hp_task_workload.
    cbn [I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload].
    exact (total_hp_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts
      fpR fpL Hfp tsk dR dL Hd).
  Qed.

  Theorem bound_on_athep_workload_correspondence (tsk : Task) (aR dR : nat) (aL dL : Lean.Nat) :
    SubNatRel aR aL -> SubNatRel dR dL ->
    SubNatRel (@S.bound_on_athep_workload Task tcR maR ppR tsR fpR tsk aR dR)
      (I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload
        Task dT tcL maL ppL tsL fpL tsk aL dL).
  Proof.
    intros Ha Hd. unfold S.bound_on_athep_workload.
    cbn [I.Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload].
    exact (svc_target_add_related _ _ _ _ (bound_on_hp_task_workload_correspondence tsk dR dL Hd)
      (bound_on_ep_task_workload_correspondence tsk aR dR aL dL Ha Hd)).
  Qed.
End ElfAthep.
