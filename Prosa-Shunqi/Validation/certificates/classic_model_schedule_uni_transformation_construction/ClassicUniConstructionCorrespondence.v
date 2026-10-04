From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.schedule.uni.schedule classic.model.schedule.uni.transformation.construction.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniConstruction.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniConstructionBase ClassicUniConstructionList.

Module I := ImportedClassicUniConstruction.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/transformation/construction.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; uniprocessor schedules pointwise through the option map (two-way
    totals).  The construction function [build_schedule] is a higher-order input (a function of schedules): as in the
    accepted v0.6 [implementation/facts/generic_schedule.v] certificate, the definitions and statements are related
    specialised at related inputs (see the section [Construction] below); [schedule_prefix] is related by induction,
    closed by its kernel-checked Lean recursion equations exported with the artifact.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used), specialised at the related inputs. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma ccn_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ccn_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma ccn_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma ccn_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma ccn_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma ccn_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (ccn_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => ccn_unmap_rel T l) PR PL).
Qed.

Definition CcnParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma ccn_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CcnParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ccn_forall_cover _ _ (CcnParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint ccn_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ccn_snatl s') end.

Lemma ccn_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (ccn_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ccn_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ccn_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ccn_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ccn_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma ccn_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CcnFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma ccn_fun_canonical FR FL (HF : CcnFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma ccn_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma ccn_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CcnFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ccn_nat_sub_canonical nR mR.
  rewrite ccn_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (ccn_foldr_add FL FR (ccn_fun_canonical FR FL HF)).
  by rewrite ccn_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition ccn_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition ccn_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma ccn_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma ccn_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (ccn_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CcnSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition ccn_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition ccn_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma ccn_sched_canonical sR : CcnSchedRel sR (ccn_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /ccn_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma ccn_sched_surjective sL : CcnSchedRel (ccn_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /ccn_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma ccn_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CcnSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ccn_forall_cover _ _ CcnSchedRel ccn_sched_to_target ccn_sched_to_source ccn_sched_canonical ccn_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ccn_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CcnSchedRel Job sR (ccn_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CcnSchedRel Job (ccn_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (ccn_sched_canonical Job) (ccn_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcnSchedRel Job sR sL.

Lemma ccn_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (ccn_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (ccn_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma ccn_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (ccn_US_scheduled_at j tR tL Ht)). Qed.

Lemma ccn_service_at_fun j : CcnFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (ccn_US_service_at j kR kL Hk). Qed.

Lemma ccn_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (ccn_ico _ _ _ _ _ _ H1 H2 (ccn_service_at_fun j)). Qed.

Lemma ccn_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (ccn_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

End USchedDefs.


(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma ccn_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (ccn_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition ccn_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma ccn_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma ccn_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

(* ------------------------------------------------------------------ *)
(** * Construction from prefixes, specialised at related inputs

    As in the accepted v0.6 [implementation/facts/generic_schedule.v] certificate: the construction function
    [build_schedule : schedule Job -> time -> option Job] is a higher-order input; the certificates below are stated for
    any source function and any Lean function that agree (through the option map) on related schedules and related
    instants ([Hbuild]), and for related base schedules ([Hbase]); the predicate [P] of the last statement is related
    pointwise through the option map ([HP]).  Inside the statements every quantified schedule, instant and job is covered
    in both directions. *)

Section Construction.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Variable buildR : UniprocessorSchedule.schedule Job -> nat -> option Job.
Variable buildL : LSched -> Lean.Nat -> I.Option Job.
Hypothesis Hbuild : forall sR sL, CcnSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CcnSchedRel Job baseR baseL.

Lemma ccn_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Theorem ScheduleConstruction_update_schedule_correspondence prevR prevL (Hprev : CcnSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CcnSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (ccn_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma ccn_prefix_canonical (mR : nat) :
  CcnSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (ccn_trs (ccn_lsym (I.Prosa_Validation_ClassicUniConstructionInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CcnSchedRel Job _ z) _).
    exact (ScheduleConstruction_update_schedule_correspondence baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (ccn_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (ccn_trs Hm1 (fun z => CcnSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (ccn_trs (ccn_lsym (I.Prosa_Validation_ClassicUniConstructionInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CcnSchedRel Job _ z) _).
    exact (ScheduleConstruction_update_schedule_correspondence _ _ IH _ _ Hm1).
Qed.

Theorem ScheduleConstruction_schedule_prefix_correspondence mR mL (Hm : SubNatRel mR mL) :
  CcnSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (ccn_trs Hm (fun z => CcnSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (ccn_prefix_canonical mR)). Qed.

Theorem ScheduleConstruction_build_schedule_from_prefixes_correspondence :
  CcnSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (ScheduleConstruction_schedule_prefix_correspondence tR tL Ht tR tL Ht). Qed.

Notation SCH := ScheduleConstruction_build_schedule_from_prefixes_correspondence.

(** ** Statements *)

Definition src_prefix_construction_same_prefix : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.prefix_construction_same_prefix Job buildR baseR)).
Definition tgt_prefix_construction_same_prefix : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_prefix_construction_same_prefix Job dJ buildL baseL)).
Theorem ScheduleConstruction_prefix_construction_same_prefix_correspondence :
  PropSPropRel src_prefix_construction_same_prefix tgt_prefix_construction_same_prefix.
Proof.
  unfold src_prefix_construction_same_prefix, tgt_prefix_construction_same_prefix.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => mR mL Hm.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Hm).
  exact (ccn_opt_rel_eq _ _ _ _ _ (ScheduleConstruction_schedule_prefix_correspondence mR mL Hm tR tL Ht) (SCH tR tL Ht)).
Qed.

Definition src_service_dependent_schedule_construction : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.service_dependent_schedule_construction Job buildR baseR)).
Definition tgt_service_dependent_schedule_construction : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_service_dependent_schedule_construction Job dJ buildL baseL)).
Theorem ScheduleConstruction_service_dependent_schedule_construction_correspondence :
  PropSPropRel src_service_dependent_schedule_construction tgt_service_dependent_schedule_construction.
Proof.
  unfold src_service_dependent_schedule_construction, tgt_service_dependent_schedule_construction.
  apply: ct_imp.
  { apply: (ccn_forall_sched Job) => s1R s1L Hs1. apply: (ccn_forall_sched Job) => s2R s2L Hs2.
    apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp.
    { apply: ct_forall_identity => j.
      exact (sub_nat_eq_correspondence _ _ _ _ (ccn_US_service Job s1R s1L Hs1 j tR tL Ht) (ccn_US_service Job s2R s2L Hs2 j tR tL Ht)). }
    exact (ccn_opt_rel_eq _ _ _ _ _ (Hbuild s1R s1L Hs1 tR tL Ht) (Hbuild s2R s2L Hs2 tR tL Ht)). }
  apply: ct_forall_nat => tR tL Ht.
  exact (ccn_opt_rel_eq _ _ _ _ _ (SCH tR tL Ht) (Hbuild _ _ SCH tR tL Ht)).
Qed.

Definition src_prefix_dependent_schedule_construction : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.prefix_dependent_schedule_construction Job buildR baseR)).
Definition tgt_prefix_dependent_schedule_construction : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_prefix_dependent_schedule_construction Job dJ buildL baseL)).
Theorem ScheduleConstruction_prefix_dependent_schedule_construction_correspondence :
  PropSPropRel src_prefix_dependent_schedule_construction tgt_prefix_dependent_schedule_construction.
Proof.
  unfold src_prefix_dependent_schedule_construction, tgt_prefix_dependent_schedule_construction.
  apply: ct_imp.
  { apply: (ccn_forall_sched Job) => s1R s1L Hs1. apply: (ccn_forall_sched Job) => s2R s2L Hs2.
    apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp.
    { apply: ct_forall_nat => t0R t0L Ht0.
      apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht0 Ht).
      exact (ccn_opt_rel_eq _ _ _ _ _ (Hs1 t0R t0L Ht0) (Hs2 t0R t0L Ht0)). }
    exact (ccn_opt_rel_eq _ _ _ _ _ (Hbuild s1R s1L Hs1 tR tL Ht) (Hbuild s2R s2L Hs2 tR tL Ht)). }
  apply: ct_forall_nat => tR tL Ht.
  exact (ccn_opt_rel_eq _ _ _ _ _ (SCH tR tL Ht) (Hbuild _ _ SCH tR tL Ht)).
Qed.

Variables (PR : option Job -> Prop) (PL : I.Option Job -> SProp).
Hypothesis HP : forall oR oL, Lean.eq (cl_opt oR) oL -> PropSPropRel (PR oR) (PL oL).

Definition src_immediate_property_of_schedule_construction : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.immediate_property_of_schedule_construction Job buildR baseR PR)).
Definition tgt_immediate_property_of_schedule_construction : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_immediate_property_of_schedule_construction Job dJ buildL baseL PL)).
Theorem ScheduleConstruction_immediate_property_of_schedule_construction_correspondence :
  PropSPropRel src_immediate_property_of_schedule_construction tgt_immediate_property_of_schedule_construction.
Proof.
  unfold src_immediate_property_of_schedule_construction, tgt_immediate_property_of_schedule_construction.
  apply: ct_imp.
  { apply: (ccn_forall_sched Job) => sR sL Hs. apply: ct_forall_nat => tR tL Ht.
    exact (HP _ _ (Hbuild sR sL Hs tR tL Ht)). }
  apply: ct_forall_nat => tR tL Ht.
  exact (HP _ _ (SCH tR tL Ht)).
Qed.
End Construction.
