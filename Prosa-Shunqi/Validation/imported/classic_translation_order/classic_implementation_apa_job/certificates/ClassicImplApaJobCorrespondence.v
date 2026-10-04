From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From prosa Require Import util.seqset classic.model.schedule.apa.affinity classic.implementation.apa.task classic.implementation.apa.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplApaJob.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplApaJobBase ClassicImplApaJobList1 ClassicImplApaJobOrd.

Module I := ImportedClassicImplApaJob.
Module T := prosa.classic.implementation.apa.task.ConcreteTask.
Module J := prosa.classic.implementation.apa.job.ConcreteJob.
Import (canonicals) T. Import (canonicals) J.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/apa/job.v] (ProsaBuddy classic, commit f692cb7).

    Inputs and relations: processor counts by [SubNatRel]; concrete APA jobs (implicit section parameter
    [num_cpus]) by their fieldwise canonical import at related processor counts: the Nat fields by the canonical Nat
    map, the job task by the accepted APA concrete-task relation (re-stated below for this export: Nat fields by the
    canonical Nat map, the affinity by its underlying sequence through the ordinal conversion); every source value has a
    related compiled value and conversely (two-way totals).  [job_eqdef] is related through the source's own definition
    (never through [eqn_job] or the Lean reflection proof); the informative reflection [eqn_job] is related by
    constructor-preserving maps in both directions, at every processor count.  The HB registration of [hasDecEq] is the
    Lean derived [DecidableEq] instance. *)

Notation LTask := I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task.
Notation LAff := I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity.

Lemma cat_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (Hc : forall a, Rel a (toB a)) (Hs : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (Hs b)) (HR (toA b))).
  - intros HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (Hc a)) (HL (toB a))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Affinities (as in the accepted classic APA certificates) *)

Section Aff.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation c := (co_ord_to_fin nR nL Hn).
Notation d := (co_fin_to_ord nR nL Hn).
Notation LVal := (I.Prosa_Util_Seqset_set_val_inst1 (Fin nL) (I.instDecidableEqFin nL)).

Lemma caf_cd (y : Fin nL) : Logic.eq (c (d y)) y.
Proof. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (d y)) (co_ord_surjective nR nL Hn y)). Qed.

Lemma caf_dc (x : 'I_nR) : Logic.eq (d (c x)) x.
Proof. exact (co_ord_eq _ _ _ _ _ (co_ord_surjective nR nL Hn (c x)) (co_ord_canonical nR nL Hn x)). Qed.

Definition caf_to_target (aR : Affinity.affinity nR) : LAff nL :=
  I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) (cl1_map c (@prosa.util.seqset._set_seq _ aR))
    (prop_to_sprop _ _ (cl1_uniq_rel _ _ c d caf_dc caf_cd _) (@prosa.util.seqset.set_uniq _ aR)).

Definition caf_to_source (aL : LAff nL) : Affinity.affinity nR :=
  @prosa.util.seqset.Build_set _ (cl1_unmap d (LVal aL))
    (interpret_strict _ (cl1_uniq_backward _ _ c d caf_cd _
                           (@I.nodup0 (Fin nL) (I.instDecidableEqFin nL) aL))).

Lemma caf_source_roundtrip aR : Logic.eq (caf_to_source (caf_to_target aR)) aR.
Proof.
  apply: val_inj. rewrite /caf_to_source /caf_to_target /=. exact (cl1_unmap_map c d caf_dc _).
Qed.

Lemma caf_set_mk_eq xs ys p q : Logic.eq xs ys ->
  Logic.eq (I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) xs p)
           (I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) ys q).
Proof. intro E. destruct E. reflexivity. Qed.

Lemma caf_target_roundtrip aL : Logic.eq (caf_to_target (caf_to_source aL)) aL.
Proof.
  destruct aL as [xs p]. rewrite /caf_to_target /caf_to_source /=.
  apply: caf_set_mk_eq. exact (cl1_map_unmap c d caf_cd xs).
Qed.
End Aff.

(* ------------------------------------------------------------------ *)
(** * Concrete tasks *)

Section Task.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Definition it_export (tR : @T.concrete_task nR) : LTask nL :=
  I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_mk nL
    (sub_nat_to_imported (T.task_id tR)) (sub_nat_to_imported (T.task_cost tR))
    (sub_nat_to_imported (T.task_period tR)) (sub_nat_to_imported (T.task_deadline tR))
    (caf_to_target nR nL Hn (T.task_affinity tR)).

Definition it_import (tL : LTask nL) : @T.concrete_task nR :=
  match tL with I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_mk a b c' d' e =>
  {| T.task_id := sub_nat_to_rocq a; T.task_cost := sub_nat_to_rocq b; T.task_period := sub_nat_to_rocq c';
     T.task_deadline := sub_nat_to_rocq d'; T.task_affinity := caf_to_source nR nL Hn e |} end.

Definition ItRel (tR : @T.concrete_task nR) (tL : LTask nL) : SProp := Lean.eq (it_export tR) tL.

Lemma it_source_roundtrip tR : Logic.eq (it_import (it_export tR)) tR.
Proof.
  destruct tR as [a b c' d' e]. unfold it_import, it_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (sub_nat_rocq_roundtrip c') (sub_nat_rocq_roundtrip d')
          (caf_source_roundtrip nR nL Hn e).
  reflexivity.
Qed.

Lemma it_target_roundtrip tL : Logic.eq (it_export (it_import tL)) tL.
Proof.
  destruct tL as [a b c' d' e]. unfold it_import, it_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip c').
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d').
  rewrite Ha Hb Hc Hd (caf_target_roundtrip nR nL Hn e). reflexivity.
Qed.

Lemma it_equality xR xL yR yL : ItRel xR xL -> ItRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !it_source_roundtrip in Hdecoded.
Qed.

Lemma it_aff_equality xR xL yR yL : Lean.eq (caf_to_target nR nL Hn xR) xL -> Lean.eq (caf_to_target nR nL Hn yR) yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal (caf_to_source nR nL Hn) (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !caf_source_roundtrip in Hdecoded.
Qed.
Lemma caf_eq_rel a b :
  PropSPropRel (a == b) (Lean.eq (caf_to_target nR nL Hn a) (caf_to_target nR nL Hn b)).
Proof.
  have E := it_aff_equality a _ b _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.
End Task.

Lemma it_source_total nR nL (Hn : SubNatRel nR nL) (tR : @T.concrete_task nR) :
  ItRel nR nL Hn tR (it_export nR nL Hn tR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma it_target_total nR nL (Hn : SubNatRel nR nL) (tL : LTask nL) :
  ItRel nR nL Hn (it_import nR nL Hn tL) tL.
Proof. exact (coq_eq_to_imported_eq _ _ (it_target_roundtrip nR nL Hn tL)). Qed.

(* ------------------------------------------------------------------ *)
(** * Boolean equality and its reflection *)

Lemma it_eq_rel nR nL (Hn : SubNatRel nR nL) a b :
  PropSPropRel (a == b) (Lean.eq (it_export nR nL Hn a) (it_export nR nL Hn b)).
Proof.
  have E := it_equality nR nL Hn a _ b _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(* ------------------------------------------------------------------ *)
(** * Concrete jobs *)

Notation LJob := I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job.

Section Job.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Definition ij_export (jR : @J.concrete_job nR) : LJob nL :=
  I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_mk nL
    (sub_nat_to_imported (J.job_id jR)) (sub_nat_to_imported (J.job_arrival jR))
    (sub_nat_to_imported (J.job_cost jR)) (sub_nat_to_imported (J.job_deadline jR))
    (it_export nR nL Hn (J.job_task jR)).

Definition ij_import (jL : LJob nL) : @J.concrete_job nR :=
  match jL with I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_mk a b c' d' e =>
  {| J.job_id := sub_nat_to_rocq a; J.job_arrival := sub_nat_to_rocq b; J.job_cost := sub_nat_to_rocq c';
     J.job_deadline := sub_nat_to_rocq d'; J.job_task := it_import nR nL Hn e |} end.

Definition IjRel (jR : @J.concrete_job nR) (jL : LJob nL) : SProp := Lean.eq (ij_export jR) jL.

Lemma ij_source_roundtrip jR : Logic.eq (ij_import (ij_export jR)) jR.
Proof.
  destruct jR as [a b c' d' e]. unfold ij_import, ij_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (sub_nat_rocq_roundtrip c') (sub_nat_rocq_roundtrip d')
          (it_source_roundtrip nR nL Hn e).
  reflexivity.
Qed.

Lemma ij_target_roundtrip jL : Logic.eq (ij_export (ij_import jL)) jL.
Proof.
  destruct jL as [a b c' d' e]. unfold ij_import, ij_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip c').
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d').
  rewrite Ha Hb Hc Hd (it_target_roundtrip nR nL Hn e). reflexivity.
Qed.

Lemma ij_equality xR xL yR yL : IjRel xR xL -> IjRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal ij_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !ij_source_roundtrip in Hdecoded.
Qed.
End Job.

Theorem ConcreteJob_concrete_job_source_total nR nL (Hn : SubNatRel nR nL) (jR : @J.concrete_job nR) :
  IjRel nR nL Hn jR (ij_export nR nL Hn jR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteJob_concrete_job_target_total nR nL (Hn : SubNatRel nR nL) (jL : LJob nL) :
  IjRel nR nL Hn (ij_import nR nL Hn jL) jL.
Proof. exact (coq_eq_to_imported_eq _ _ (ij_target_roundtrip nR nL Hn jL)). Qed.

(* ------------------------------------------------------------------ *)
(** * Boolean equality and its reflection *)

Theorem ConcreteJob_job_eqdef_correspondence nR nL (Hn : SubNatRel nR nL) xR xL yR yL :
  IjRel nR nL Hn xR xL -> IjRel nR nL Hn yR yL ->
  CtBoolRel (J.job_eqdef xR yR) (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_job_eqdef nL xL yL).
Proof.
  intros Hx Hy. destruct Hx. destruct Hy. unfold J.job_eqdef.
  cbn [I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_job_eqdef].
  refine (ct_bool_and _ _ _ _ _ (ct_decide_bool _ _ _ (it_eq_rel nR nL Hn _ _))).
  refine (ct_bool_and _ _ _ _ _ (ct_decide_eq_nat _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _))).
  refine (ct_bool_and _ _ _ _ _ (ct_decide_eq_nat _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _))).
  exact (ct_bool_and _ _ _ _ (ct_decide_eq_nat _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _))
           (ct_decide_eq_nat _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _))).
Qed.

Definition it_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_List_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition it_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_List_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_List_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_List_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition it_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (it_reflect_backward_at_bool PR PL HP _). Defined.

Definition src_eqn_job : Type := ltac:(let X := type of (@J.eqn_job) in exact X).
Definition tgt_eqn_job : Type := ltac:(let X := type of (@I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_eqn_job) in exact X).

(** At every processor count (related by [SubNatRel], both directions). *)
Theorem ConcreteJob_eqn_job_correspondence :
  Datatypes.prod (src_eqn_job -> tgt_eqn_job) (tgt_eqn_job -> src_eqn_job).
Proof.
  split.
  - intros f nL xL yL.
    have Hn := sub_nat_rel_surjective nL.
    have Hx := ConcreteJob_concrete_job_target_total _ _ Hn xL. have Hy := ConcreteJob_concrete_job_target_total _ _ Hn yL.
    exact (it_reflect_forward _ _ _ _ (ij_equality _ _ Hn _ _ _ _ Hx Hy)
      (ConcreteJob_job_eqdef_correspondence _ _ Hn _ _ _ _ Hx Hy) (f _ (ij_import _ _ Hn xL) (ij_import _ _ Hn yL))).
  - intros g nR xR yR.
    have Hn := sub_nat_rel_canonical nR.
    have Hx := ConcreteJob_concrete_job_source_total _ _ Hn xR. have Hy := ConcreteJob_concrete_job_source_total _ _ Hn yR.
    exact (it_reflect_backward _ _ _ _ (ij_equality _ _ Hn _ _ _ _ Hx Hy)
      (ConcreteJob_job_eqdef_correspondence _ _ Hn _ _ _ _ Hx Hy) (g _ (ij_export _ _ Hn xR) (ij_export _ _ Hn yR))).
Qed.
