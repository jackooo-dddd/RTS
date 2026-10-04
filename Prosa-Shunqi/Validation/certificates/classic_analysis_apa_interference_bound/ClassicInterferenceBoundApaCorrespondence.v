From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From prosa Require Import classic.model.time classic.util.div_mod classic.analysis.apa.workload_bound classic.analysis.apa.interference_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicInterferenceBoundApa.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicInterferenceBoundApaNatSub ClassicInterferenceBoundApaOps ClassicInterferenceBoundApaBase.

Module I := ImportedClassicInterferenceBoundApa.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/apa/interference_bound.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type is an [eqType], identified, with the Lean [DecidableEq]
    instance given by its decision procedure ([ct_decidable_eq]); times by
    [SubNatRel]; task parameters [Task -> time] pointwise through [SubNatRel];
    a (task, response time) pair by its components ([CibPairRel]); all with
    two-way totals.  [W] and [max_jobs] as in the accepted classic workload_bound
    certificate (the classic [div_floor] and the Nat operations through the
    accepted operation-level bridge [DivModCorrespondence], re-bound to this
    export); [minn] by [ct_min_rel]. *)

Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Definition CibPairRel (T : Type) (pR : T * nat) (pL : I.Prod_inst2 T Lean.Nat) : SProp :=
  Lean.eq (I.Prod_mk_inst2 T Lean.Nat pR.1 (sub_nat_to_imported pR.2)) pL.

Definition cib_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cib_max_jobs (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cib_W (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  have Hm := cib_max_jobs Task cR cL Hc pR pL Hp tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (ct_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

Theorem InterferenceBoundGeneric_interference_bound_generic_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk dR dL (Hd : SubNatRel dR dL)
    prR prL (Hpr : CibPairRel Task prR prL) :
  SubNatRel (InterferenceBoundGeneric.interference_bound_generic cR pR tsk dR prR)
    (I.Prosa_Classic_Analysis_Apa_InterferenceBound_InterferenceBoundGeneric_interference_bound_generic Task (ct_decidable_eq Task) cL pL tsk dL prL).
Proof.
  refine (cib_trs Hpr (fun z => SubNatRel (InterferenceBoundGeneric.interference_bound_generic cR pR tsk dR prR)
                                  (I.Prosa_Classic_Analysis_Apa_InterferenceBound_InterferenceBoundGeneric_interference_bound_generic Task (ct_decidable_eq Task) cL pL tsk dL z)) _).
  exact (ct_min_rel _ _ _ _ (cib_W Task cR cL Hc pR pL Hp prR.1 _ _ (sub_nat_rel_canonical prR.2) _ _ Hd)
           (dm_add_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ Hd (Hc tsk)) (sub_nat_rel_canonical 1))).
Qed.
