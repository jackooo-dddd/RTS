(* Re-bound copy of the accepted certificates/implementation_refinements_task/RefTaskCorrespondence.v: modules renamed (ImportedRefTask=ImportedRefEDFFastSearchSpace,RtBase=ReBase,RtArrivalBound=ReArrivalBound), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/task.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged). The base
    maps and operation correspondences are those of the accepted refinements.v and arrival_bound.v certificates,
    re-bound in [ReBase] and [ReArrivalBound]. Here:
    - the concrete task and job records, and the generic task record [task_T], are related by the
      constructor-preserving maps (any element map), with two-way totals for [Task], [Job] and [task_T];
    - each definition is related to its translation for related inputs (operation-class instances by their field);
    - [Rtask] (a [Type]-valued relation) by maps in both directions, and the eight refinement instances by
      [TypeCorrespondence].
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.task.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFFastSearchSpace ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence ReBase
  ReArrivalBound.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefEDFFastSearchSpace.
Module Rt := prosa.implementation.refinements.task.
Module Dt := prosa.implementation.definitions.task.
Module Rab := prosa.implementation.refinements.arrival_bound.
Module AB := prosa.implementation.definitions.arrival_bound.

(** ** Imported names *)
Abbreviation ICT := I.Prosa_Implementation_Definitions_Task_concrete_task.
Abbreviation ICTmk := I.Prosa_Implementation_Definitions_Task_concrete_task_mk.
Abbreviation ICJ := I.Prosa_Implementation_Definitions_Task_concrete_job.
Abbreviation ICJmk := I.Prosa_Implementation_Definitions_Task_concrete_job_mk.
Abbreviation ITT := I.Prosa_Implementation_Refinements_Task_task_T.
Abbreviation ITTmk := I.Prosa_Implementation_Refinements_Task_task_T_mk.
Abbreviation IRtask := I.Prosa_Implementation_Refinements_Task_Rtask.

(** ** Concrete tasks and jobs *)
Definition task_ex (t : Dt.concrete_task) : ICT :=
  ICTmk (ne (Dt.task_id t)) (ne (Dt.task_cost t)) (ab_ex (Dt.task_arrival t)) (ne (Dt.task_deadline t))
    (ne (Dt.task_priority t)).
Definition task_im (t : ICT) : Dt.concrete_task :=
  {| Dt.task_id := ni (I.Prosa_Implementation_Definitions_Task_concrete_task_task_id t);
     Dt.task_cost := ni (I.Prosa_Implementation_Definitions_Task_concrete_task_task_cost t);
     Dt.task_arrival := ab_im (I.Prosa_Implementation_Definitions_Task_concrete_task_task_arrival t);
     Dt.task_deadline := ni (I.Prosa_Implementation_Definitions_Task_concrete_task_task_deadline t);
     Dt.task_priority := ni (I.Prosa_Implementation_Definitions_Task_concrete_task_task_priority t) |}.
Lemma rf_task_rt t : task_im (task_ex t) = t.
Proof. case: t => i c a d p. by rewrite /task_im /task_ex /= !rf_ni_ne rf_ab_rt. Qed.
Lemma rf_task_rtL t : Lean.eq (task_ex (task_im t)) t.
Proof.
  destruct t as [i c a d p]. unfold task_ex, task_im. cbn.
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk z _ _ _ _) _ _ (rf_ne_ni i)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk i z _ _ _) _ _ (rf_ne_ni c)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk i c z _ _) _ _ (rf_ab_rtL a)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk i c a z _) _ _ (rf_ne_ni d)) _).
  exact (rf_congr (fun z => ICTmk i c a d z) _ _ (rf_ne_ni p)).
Qed.

Definition job_ex (j : Dt.concrete_job) : ICJ :=
  ICJmk (ne (Dt.job_id j)) (ne (Dt.job_arrival j)) (ne (Dt.job_cost j)) (ne (Dt.job_deadline j))
    (task_ex (Dt.job_task j)).
Definition job_im (j : ICJ) : Dt.concrete_job :=
  match j with
  | I.Prosa_Implementation_Definitions_Task_concrete_job_mk i a c d t =>
      {| Dt.job_id := ni i; Dt.job_arrival := ni a; Dt.job_cost := ni c; Dt.job_deadline := ni d;
         Dt.job_task := task_im t |}
  end.
Lemma rf_job_rtL j : Lean.eq (job_ex (job_im j)) j.
Proof.
  destruct j as [i a c d t]. unfold job_ex, job_im. cbn.
  refine (rf_trans _ _ _ (rf_congr (fun z => ICJmk z _ _ _ _) _ _ (rf_ne_ni i)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICJmk i z _ _ _) _ _ (rf_ne_ni a)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICJmk i a z _ _) _ _ (rf_ne_ni c)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICJmk i a c z _) _ _ (rf_ne_ni d)) _).
  exact (rf_congr (fun z => ICJmk i a c d z) _ _ (rf_task_rtL t)).
Qed.

Definition TaskRel (t : Rt.Task) (tL : I.Prosa_Implementation_Refinements_Task_Task) : SProp := Lean.eq (task_ex t) tL.
Definition JobRel (j : Rt.Job) (jL : I.Prosa_Implementation_Refinements_Task_Job) : SProp := Lean.eq (job_ex j) jL.

Lemma Task_source_total (t : Rt.Task) : TaskRel t (task_ex t). Proof. exact (rf_refl _). Qed.
Lemma Task_target_total (tL : I.Prosa_Implementation_Refinements_Task_Task) : TaskRel (task_im tL : Rt.Task) tL.
Proof. exact (rf_task_rtL tL). Qed.
Lemma Job_source_total (j : Rt.Job) : JobRel j (job_ex j). Proof. exact (rf_refl _). Qed.
Lemma Job_target_total (jL : I.Prosa_Implementation_Refinements_Task_Job) : JobRel (job_im jL : Rt.Job) jL.
Proof. exact (rf_job_rtL jL). Qed.

(** ** The generic task record *)
Definition taskT_ex {A B : Type} (e : A -> B) (t : @Rt.task_T A) : ITT B :=
  ITTmk B (e (Rt.task_id_T t)) (e (Rt.task_cost_T t)) (tabT_ex e (Rt.task_arrival_T t)) (e (Rt.task_deadline_T t))
    (e (Rt.task_priority_T t)).
Definition taskT_im {A B : Type} (i : B -> A) (t : ITT B) : @Rt.task_T A :=
  {| Rt.task_id_T := i (I.Prosa_Implementation_Refinements_Task_task_T_task_id_T B t);
     Rt.task_cost_T := i (I.Prosa_Implementation_Refinements_Task_task_T_task_cost_T B t);
     Rt.task_arrival_T := tabT_im i (I.Prosa_Implementation_Refinements_Task_task_T_task_arrival_T B t);
     Rt.task_deadline_T := i (I.Prosa_Implementation_Refinements_Task_task_T_task_deadline_T B t);
     Rt.task_priority_T := i (I.Prosa_Implementation_Refinements_Task_task_T_task_priority_T B t) |}.
Lemma rf_taskT_rt {A B : Type} (e : A -> B) (i : B -> A) (H : forall a, i (e a) = a) t : taskT_im i (taskT_ex e t) = t.
Proof. case: t => a b c d f. by rewrite /taskT_im /taskT_ex /= !H (rf_tabT_rt e i H). Qed.
Lemma rf_taskT_rtL {A B : Type} (e : A -> B) (i : B -> A) (H : forall b, Lean.eq (e (i b)) b) t :
  Lean.eq (taskT_ex e (taskT_im i t)) t.
Proof.
  destruct t as [a b c d f]. unfold taskT_ex, taskT_im. cbn.
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk B z _ _ _ _) _ _ (H a)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk B a z _ _ _) _ _ (H b)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk B a b z _ _) _ _ (rf_tabT_rtL e i H c)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk B a b c z _) _ _ (H d)) _).
  exact (rf_congr (fun z => ITTmk B a b c d z) _ _ (H f)).
Qed.

Definition TaskTRel {A : Type} (t : @Rt.task_T A) (tL : ITT A) : SProp := Lean.eq (taskT_ex idr t) tL.
Lemma task_T_source_total (A : Type) (t : @Rt.task_T A) : TaskTRel t (taskT_ex idr t). Proof. exact (rf_refl _). Qed.
Lemma task_T_target_total (A : Type) (tL : ITT A) : TaskTRel (taskT_im idr tL) tL.
Proof. exact (rf_taskT_rtL idr idr rf_idr_rtL tL). Qed.


(** ** Generic definitions (element types by identity, operation classes by their field) *)

Lemma task_eqdef_T_correspondence (T : Type) (eR : eq_of T) eL (aR : eq_of (@Rab.task_arrivals_bound_T T)) aL :
  BOpRel eR (Ieq_op T eL) ->
  (forall x y, Lean.eq (be (aR x y)) (Ieq_op (ITab T) aL (tabT_ex idr x) (tabT_ex idr y))) ->
  forall t1R t1L t2R t2L, TaskTRel t1R t1L -> TaskTRel t2R t2L ->
  Lean.eq (be (@Rt.task_eqdef_T T eR aR t1R t2R)) (I.Prosa_Implementation_Refinements_Task_task_eqdef_T T eL aL t1L t2L).
Proof.
  intros He Ha t1R t1L t2R t2L H1 H2. destruct H1. destruct H2.
  destruct t1R as [i1 c1 a1 d1 p1]; destruct t2R as [i2 c2 a2 d2 p2]. unfold Rt.task_eqdef_T. cbn.
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (He p1 p2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (He d1 d2))).
  refine (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ _ (Ha a1 a2))).
  exact (rf_trans _ _ _ (rf_and_ex _ _) (rf_congr2 I.Bool_and _ _ _ _ (He i1 i2) (He c1 c2))).
Qed.

Lemma rf_inter_ex (T : Type) (oR : one_of T) oL : OneRel oR oL -> forall p,
  Lean.eq (pfx idr (@Rt.inter_arrival_to_extrapolated_arrival_curve_T T oR p))
    (I.Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T T oL p).
Proof.
  intros Ho p. have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
  unfold I.Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T. rf_rw Ho'.
  exact (rf_refl _).
Qed.

Lemma inter_arrival_to_extrapolated_arrival_curve_T_correspondence (T : Type) (oR : one_of T) oL :
  OneRel oR oL -> forall pR pL, Lean.eq pR pL ->
  Lean.eq (pfx idr (@Rt.inter_arrival_to_extrapolated_arrival_curve_T T oR pR))
    (I.Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T T oL pL).
Proof. intros Ho pR pL H. destruct H. exact (rf_inter_ex T oR oL Ho pR). Qed.

Lemma rf_getEAC_ex (T : Type) (oR : one_of T) oL : OneRel oR oL -> forall t,
  @PfxRel T (@Rt.get_extrapolated_arrival_curve_T T oR t)
    (I.Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T T oL (taskT_ex idr t)).
Proof.
  intros Ho [i c a d p]. unfold Rt.get_extrapolated_arrival_curve_T. cbn.
  destruct a as [x|x|e]; cbn [tabT_ex].
  - exact (rf_inter_ex T oR oL Ho x).
  - exact (rf_inter_ex T oR oL Ho x).
  - exact (rf_refl _).
Qed.

Lemma get_extrapolated_arrival_curve_T_correspondence (T : Type) (oR : one_of T) oL :
  OneRel oR oL -> forall tR tL, TaskTRel tR tL ->
  @PfxRel T (@Rt.get_extrapolated_arrival_curve_T T oR tR)
    (I.Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T T oL tL).
Proof. intros Ho tR tL H. destruct H. exact (rf_getEAC_ex T oR oL Ho tR). Qed.

Lemma rf_CMA_ex (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL (mR : mul_of T) mL
    (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> forall t d,
  Lean.eq (@Rt.ConcreteMaxArrivals_T T zR oR aR mR dR moR lR t d)
    (I.Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T T zL oL aL mL dL moL lL (taskT_ex idr t) d).
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl t d.
  exact (extrapolated_arrival_curve_T_correspondence T zR zL aR aL mR mL dR dL moR moL lR lL Hz Ha Hm Hd Hmo Hl
    _ _ d d (rf_getEAC_ex T oR oL Ho t) (rf_refl _)).
Qed.

Lemma ConcreteMaxArrivals_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> forall tR tL dR' dL', TaskTRel tR tL -> Lean.eq dR' dL' ->
  Lean.eq (@Rt.ConcreteMaxArrivals_T T zR oR aR mR dR moR lR tR dR')
    (I.Prosa_Implementation_Refinements_Task_ConcreteMaxArrivals_T T zL oL aL mL dL moL lL tL dL').
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl tR tL dR' dL' Ht Hd'. destruct Ht. destruct Hd'.
  exact (rf_CMA_ex T zR zL oR oL aR aL mR mL dR dL moR moL lR lL Hz Ho Ha Hm Hd Hmo Hl tR dR').
Qed.

Lemma task_rbf_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (mR : mul_of T) mL (dR : div_of T) dL (moR : mod_of T) moL (lR : leq_of T) lL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel mR (Imul_op T mL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel moR (Imod_op T moL) -> BOpRel lR (Ileq_op T lL) -> forall tR tL dR' dL', TaskTRel tR tL -> Lean.eq dR' dL' ->
  Lean.eq (@Rt.task_rbf_T T zR oR aR mR dR moR lR tR dR')
    (I.Prosa_Implementation_Refinements_Task_task_rbf_T T zL oL aL mL dL moL lL tL dL').
Proof.
  intros Hz Ho Ha Hm Hd Hmo Hl tR tL dR' dL' Ht Hd'. destruct Ht. destruct Hd'.
  unfold Rt.task_rbf_T, I.Prosa_Implementation_Refinements_Task_task_rbf_T.
  exact (rf_trans _ _ _ (Hm _ _) (rf_congr (Imul_op T mL (Rt.task_cost_T tR)) _ _
    (rf_CMA_ex T zR zL oR oL aR aL mR mL dR dL moR moL lR lL Hz Ho Ha Hm Hd Hmo Hl tR dR'))).
Qed.

Lemma valid_arrivals_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (eR : eq_of T) eL
    (lR : leq_of T) lL (tR' : lt_of T) tL' :
  ZeroRel zR zL -> OneRel oR oL -> BOpRel eR (Ieq_op T eL) -> BOpRel lR (Ileq_op T lL) -> BOpRel tR' (Ilt_op T tL') ->
  forall tR tL, TaskTRel tR tL ->
  Lean.eq (be (@Rt.valid_arrivals_T T zR oR eR lR tR' tR))
    (I.Prosa_Implementation_Refinements_Task_valid_arrivals_T T zL oL eL lL tL' tL).
Proof.
  intros Hz Ho He Hl Ht tR tL H. destruct H. have Ho' : Lean.eq oR (Ione_op T oL) := Ho.
  destruct tR as [i c a d p]. unfold Rt.valid_arrivals_T. cbn.
  destruct a as [x|x|e]; cbn [tabT_ex].
  - exact (rf_trans _ _ _ (Hl oR x) (rf_congr (fun z => Ileq_op T lL z x) _ _ Ho')).
  - exact (rf_trans _ _ _ (Hl oR x) (rf_congr (fun z => Ileq_op T lL z x) _ _ Ho')).
  - exact (valid_extrapolated_arrival_curve_T_correspondence T zR zL oR oL eR eL lR lL tR' tL' Hz Ho He Hl Ht e _ (rf_refl _)).
Qed.

Lemma get_horizon_of_task_T_correspondence (T : Type) (oR : one_of T) oL :
  OneRel oR oL -> forall tR tL, TaskTRel tR tL ->
  Lean.eq (@Rt.get_horizon_of_task_T T oR tR) (I.Prosa_Implementation_Refinements_Task_get_horizon_of_task_T T oL tL).
Proof. intros Ho tR tL H. destruct H. exact (horizon_of_T_correspondence T _ _ (rf_getEAC_ex T oR oL Ho tR)). Qed.

Lemma rf_gtsT_ex (T : Type) (oR : one_of T) oL : OneRel oR oL -> forall t,
  Lean.eq (lex idr (@Rt.get_time_steps_of_task_T T oR t))
    (I.Prosa_Implementation_Refinements_Task_get_time_steps_of_task_T T oL (taskT_ex idr t)).
Proof. intros Ho t. exact (time_steps_of_T_correspondence T _ _ (rf_getEAC_ex T oR oL Ho t)). Qed.

Lemma get_time_steps_of_task_T_correspondence (T : Type) (oR : one_of T) oL :
  OneRel oR oL -> forall tR tL, TaskTRel tR tL ->
  Lean.eq (lex idr (@Rt.get_time_steps_of_task_T T oR tR))
    (I.Prosa_Implementation_Refinements_Task_get_time_steps_of_task_T T oL tL).
Proof. intros Ho tR tL H. destruct H. exact (rf_gtsT_ex T oR oL Ho tR). Qed.

Lemma rf_tswo_ex (T : Type) (oR : one_of T) oL (aR : add_of T) aL : OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> forall t d,
  Lean.eq (lex idr (@Rt.time_steps_with_offset_T T oR aR t d))
    (I.Prosa_Implementation_Refinements_Task_time_steps_with_offset_T T oL aL (taskT_ex idr t) d).
Proof.
  intros Ho Ha t d. unfold Rt.time_steps_with_offset_T, I.Prosa_Implementation_Refinements_Task_time_steps_with_offset_T.
  refine (rf_trans _ _ _ (rf_map_ex idr idr _ (fun x => Iadd_op T aL x d) (fun x => Ha x d) _) _).
  exact (rf_congr (I.List_map_inst3 T T (fun x => Iadd_op T aL x d)) _ _ (rf_gtsT_ex T oR oL Ho t)).
Qed.

Lemma time_steps_with_offset_T_correspondence (T : Type) (oR : one_of T) oL (aR : add_of T) aL :
  OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> forall tR tL dR dL, TaskTRel tR tL -> Lean.eq dR dL ->
  Lean.eq (lex idr (@Rt.time_steps_with_offset_T T oR aR tR dR))
    (I.Prosa_Implementation_Refinements_Task_time_steps_with_offset_T T oL aL tL dL).
Proof. intros Ho Ha tR tL dR dL Ht Hd. destruct Ht. destruct Hd. exact (rf_tswo_ex T oR oL aR aL Ho Ha tR dR). Qed.

Lemma repeat_steps_with_offset_T_correspondence (T : Type) (oR : one_of T) oL (aR : add_of T) aL :
  OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> forall tR tL oR' oL', TaskTRel tR tL -> Lean.eq (lex idr oR') oL' ->
  Lean.eq (lex idr (@Rt.repeat_steps_with_offset_T T oR aR tR oR'))
    (I.Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T T oL aL tL oL').
Proof.
  intros Ho Ha tR tL oR' oL' Ht Hos. destruct Ht. destruct Hos.
  unfold Rt.repeat_steps_with_offset_T, I.Prosa_Implementation_Refinements_Task_repeat_steps_with_offset_T.
  refine (rf_trans _ _ _ (rf_flatten_ex idr _) _).
  refine (rf_congr (I.List_flatten_inst1 T) _ _ _).
  exact (rf_map_ex idr (lex idr) _ _ (fun d => rf_tswo_ex T oR oL aR aL Ho Ha tR d) _).
Qed.

(** ** Definitions at the binary numbers *)
Lemma rf_taskT2task_ex t :
  Lean.eq (task_ex (Rt.taskT_to_task t)) (I.Prosa_Implementation_Refinements_Task_taskT_to_task (taskT_ex Ne_ t)).
Proof.
  destruct t as [i c a d p]. cbn.
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk z _ _ _ _) _ _ (rf_nat_of_bin_ex i)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk _ z _ _ _) _ _ (rf_nat_of_bin_ex c)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk _ _ z _ _) _ _ (rf_abT2ab_ex a)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ICTmk _ _ _ z _) _ _ (rf_nat_of_bin_ex d)) _).
  exact (rf_congr (fun z => ICTmk _ _ _ _ z) _ _ (rf_nat_of_bin_ex p)).
Qed.

Lemma taskT_to_task_correspondence tR tL :
  Lean.eq (taskT_ex Ne_ tR) tL ->
  Lean.eq (task_ex (Rt.taskT_to_task tR)) (I.Prosa_Implementation_Refinements_Task_taskT_to_task tL).
Proof. intro H. destruct H. exact (rf_taskT2task_ex tR). Qed.

Lemma rf_task2taskT_ex t :
  Lean.eq (taskT_ex Ne_ (Rt.task_to_taskT t)) (I.Prosa_Implementation_Refinements_Task_task_to_taskT (task_ex t)).
Proof.
  destruct t as [i c a d p]. cbn.
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk IN z _ _ _ _) _ _ (rf_bin_of_nat_ex i)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk IN _ z _ _ _) _ _ (rf_bin_of_nat_ex c)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk IN _ _ z _ _) _ _ (rf_ab2abT_ex a)) _).
  refine (rf_trans _ _ _ (rf_congr (fun z => ITTmk IN _ _ _ z _) _ _ (rf_bin_of_nat_ex d)) _).
  exact (rf_congr (fun z => ITTmk IN _ _ _ _ z) _ _ (rf_bin_of_nat_ex p)).
Qed.

Lemma task_to_taskT_correspondence tR tL :
  Lean.eq (task_ex tR) tL ->
  Lean.eq (taskT_ex Ne_ (Rt.task_to_taskT tR)) (I.Prosa_Implementation_Refinements_Task_task_to_taskT tL).
Proof. intro H. destruct H. exact (rf_task2taskT_ex tR). Qed.

(** ** Statement correspondences *)
(** Shape [refines (Rtask ==> R) f g] for a field. *)
(** Shape [refines (Rnat ==> Rtask_ab) f g] for the constructors. *)