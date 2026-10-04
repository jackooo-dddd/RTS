From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.model.arrival.basic.task.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicTask.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicTaskBase ClassicTaskList ClassicTaskSeqset.

Module I := ImportedClassicTask.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/basic/task.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type is an [eqType], identified, with the Lean
    [DecidableEq] instance given by the eqType's decision procedure
    ([ct_decidable_eq]); task parameters [Task -> time] pointwise through
    [SubNatRel]; task sequences elementwise ([ClListRel]); task sets by the
    accepted [RocqSeqSetRel] (re-bound [ClassicTaskSeqset], two-way totals).
    All definitions compute to related values on related inputs. *)

Notation cid := (fun z => z).

Definition CtParRel (Task : Type) (pR : Task -> nat) (pL : Task -> Lean.Nat) : SProp := forall t, SubNatRel (pR t) (pL t).

Lemma ct_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Section Defs.
Variables (Task : eqType).
Notation dT := (ct_decidable_eq Task).
Notation c0 := (sub_nat_rel_canonical 0).

Theorem SporadicTask_task_cost_positive_correspondence cR cL (Hc : CtParRel Task cR cL) tsk :
  CtBoolRel (SporadicTask.task_cost_positive cR tsk) (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_cost_positive Task dT cL tsk).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc tsk)). Qed.

Theorem SporadicTask_task_period_positive_correspondence pR pL (Hp : CtParRel Task pR pL) tsk :
  CtBoolRel (SporadicTask.task_period_positive pR tsk) (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_period_positive Task dT pL tsk).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hp tsk)). Qed.

Theorem SporadicTask_task_deadline_positive_correspondence dR dL (Hd : CtParRel Task dR dL) tsk :
  CtBoolRel (SporadicTask.task_deadline_positive dR tsk) (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_deadline_positive Task dT dL tsk).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd tsk)). Qed.

Theorem SporadicTask_task_cost_le_deadline_correspondence cR cL dR dL (Hc : CtParRel Task cR cL) (Hd : CtParRel Task dR dL) tsk :
  CtBoolRel (SporadicTask.task_cost_le_deadline cR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_cost_le_deadline Task dT cL dL tsk).
Proof. exact (ct_decide_le _ _ _ _ (Hc tsk) (Hd tsk)). Qed.

Theorem SporadicTask_task_cost_le_period_correspondence cR cL pR pL (Hc : CtParRel Task cR cL) (Hp : CtParRel Task pR pL) tsk :
  CtBoolRel (SporadicTask.task_cost_le_period cR pR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_cost_le_period Task dT cL pL tsk).
Proof. exact (ct_decide_le _ _ _ _ (Hc tsk) (Hp tsk)). Qed.

Theorem SporadicTask_is_valid_sporadic_task_correspondence cR cL pR pL dR dL
    (Hc : CtParRel Task cR cL) (Hp : CtParRel Task pR pL) (Hd : CtParRel Task dR dL) tsk :
  PropSPropRel (SporadicTask.is_valid_sporadic_task cR pR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_is_valid_sporadic_task Task dT cL pL dL tsk).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (SporadicTask_task_cost_positive_correspondence cR cL Hc tsk)).
  apply: ct_and; first exact (ct_bool_truth _ _ (SporadicTask_task_period_positive_correspondence pR pL Hp tsk)).
  apply: ct_and; first exact (ct_bool_truth _ _ (SporadicTask_task_deadline_positive_correspondence dR dL Hd tsk)).
  apply: ct_and; first exact (ct_bool_truth _ _ (SporadicTask_task_cost_le_deadline_correspondence cR cL dR dL Hc Hd tsk)).
  exact (ct_bool_truth _ _ (SporadicTask_task_cost_le_period_correspondence cR cL pR pL Hc Hp tsk)).
Qed.

(** [taskset_of Task] is the accepted sequence-set type: the source and target
    types are related by [RocqSeqSetRel] with two-way totals (the target instance
    [ct_decidable_eq] is convertible with the adapter's [seqset_decidable_eq]). *)
Lemma ct_taskset_target_total (s : I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_taskset_of Task dT) :
  RocqSeqSetRel Task (imported_to_source_seqset Task s) s.
Proof. destruct s as [xs Hnodup]. exact (seqset_list_roundtrip xs). Qed.

Theorem SporadicTaskset_taskset_of_correspondence :
  And (forall s : SporadicTaskset.taskset_of Task, RocqSeqSetRel Task s (source_to_imported_seqset Task s))
      (forall s : I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_taskset_of Task dT,
         RocqSeqSetRel Task (imported_to_source_seqset Task s) s).
Proof. exact (And_intro _ _ (seqset_relation_source_total Task) ct_taskset_target_total). Qed.

Theorem SporadicTaskset_valid_sporadic_taskset_correspondence cR cL pR pL dR dL
    (Hc : CtParRel Task cR cL) (Hp : CtParRel Task pR pL) (Hd : CtParRel Task dR dL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (SporadicTaskset.valid_sporadic_taskset cR pR dR ts)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_valid_sporadic_taskset Task dT cL pL dL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (ct_mem Task tsk ts tsL Hts) (SporadicTask_is_valid_sporadic_task_correspondence cR cL pR pL dR dL Hc Hp Hd tsk)).
Qed.

Theorem SporadicTaskset_implicit_deadline_model_correspondence pR pL dR dL
    (Hp : CtParRel Task pR pL) (Hd : CtParRel Task dR dL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (SporadicTaskset.implicit_deadline_model pR dR ts)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_implicit_deadline_model Task dT pL dL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (ct_mem Task tsk ts tsL Hts) (sub_nat_eq_correspondence _ _ _ _ (Hd tsk) (Hp tsk))).
Qed.

Theorem SporadicTaskset_constrained_deadline_model_correspondence pR pL dR dL
    (Hp : CtParRel Task pR pL) (Hd : CtParRel Task dR dL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (SporadicTaskset.constrained_deadline_model pR dR ts)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_constrained_deadline_model Task dT pL dL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (ct_mem Task tsk ts tsL Hts) (sub_nat_le_correspondence _ _ _ _ (Hd tsk) (Hp tsk))).
Qed.
End Defs.

Theorem SporadicTaskset_arbitrary_deadline_model_correspondence :
  PropSPropRel SporadicTaskset.arbitrary_deadline_model I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_arbitrary_deadline_model.
Proof.
  apply prop_sprop_rel_intro.
  - intros _. exact I.True_intro.
  - intros _. exact (strictly_inhabits Logic.I).
Qed.
