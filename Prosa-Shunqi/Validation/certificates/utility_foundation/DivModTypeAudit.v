From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import GeneratedDivModSource.
From FoundationImported Require Import ImportedDivMod.
From FoundationCertificates Require Import
  SubadditivityNatCorrespondence DivModCorrespondence DivModCertificate.

(** Exact target-type guards.  These definitions typecheck only if the
    structural propositions used by the independent certificates are exact
    specializations of the statements exported from the compiled Lean
    artifact.  They are provenance guards and are not dependencies of the
    semantic certificates. *)

Check GeneratedDivModSource.statement_eqdivn_leqmodn.
Check GeneratedDivModSource.statement_ltdivn_dvdn.
Check GeneratedDivModSource.statement_addn1_modn_commute.
Check GeneratedDivModSource.statement_addmod_le_mod.
Check GeneratedDivModSource.statement_divn_leq.
Check GeneratedDivModSource.div_floor.
Check GeneratedDivModSource.div_ceil.
Check GeneratedDivModSource.statement_div_ceil0.
Check GeneratedDivModSource.statement_div_ceil_gt0.
Check GeneratedDivModSource.statement_div_ceil_monotone1.
Check GeneratedDivModSource.statement_leq_div_ceil_add1.
Check GeneratedDivModSource.statement_div_ceil_subadditive.
Check GeneratedDivModSource.statement_div_ceil_multiple.
Check GeneratedDivModSource.statement_div_floor_add_g.
Check GeneratedDivModSource.statement_mod_elim.

Definition exact_target_eqdivn_leqmodn_guard :
    dm_target_eqdivn_leqmodn :=
  fun t1 t2 h =>
    ImportedDivMod.Prosa_Util_Div_mod_eqdivn_leqmodn
      (sub_nat_to_imported t1) (sub_nat_to_imported t2)
      (sub_nat_to_imported h).

Definition exact_target_ltdivn_dvdn_guard : dm_target_ltdivn_dvdn :=
  fun x y => ImportedDivMod.Prosa_Util_Div_mod_ltdivn_dvdn
    (sub_nat_to_imported x) (sub_nat_to_imported y).

Definition exact_target_addn1_modn_commute_guard :
    dm_target_addn1_modn_commute :=
  fun x h => ImportedDivMod.Prosa_Util_Div_mod_addn1_modn_commute
    (sub_nat_to_imported x) (sub_nat_to_imported h).

Definition exact_target_addmod_le_mod_guard : dm_target_addmod_le_mod :=
  fun x y h => ImportedDivMod.Prosa_Util_Div_mod_addmod_le_mod
    (sub_nat_to_imported x) (sub_nat_to_imported y)
    (sub_nat_to_imported h).

Definition exact_target_divn_leq_guard : dm_target_divn_leq :=
  fun k T x => ImportedDivMod.Prosa_Util_Div_mod_divn_leq
    (sub_nat_to_imported k) (sub_nat_to_imported T)
    (sub_nat_to_imported x).

Definition exact_target_div_ceil0_guard : dm_target_div_ceil0 :=
  fun b => ImportedDivMod.Prosa_Util_Div_mod_div_ceil0
    (sub_nat_to_imported b).

Definition exact_target_div_ceil_gt0_guard : dm_target_div_ceil_gt0 :=
  fun a b => ImportedDivMod.Prosa_Util_Div_mod_div_ceil_gt0
    (sub_nat_to_imported a) (sub_nat_to_imported b).

Definition exact_target_div_ceil_monotone1_guard :
    dm_target_div_ceil_monotone1 :=
  fun d m n => ImportedDivMod.Prosa_Util_Div_mod_div_ceil_monotone1
    (sub_nat_to_imported d) (sub_nat_to_imported m)
    (sub_nat_to_imported n).

Definition exact_target_leq_div_ceil_add1_guard :
    dm_target_leq_div_ceil_add1 :=
  fun delta T => ImportedDivMod.Prosa_Util_Div_mod_leq_div_ceil_add1
    (sub_nat_to_imported delta) (sub_nat_to_imported T).

Definition exact_target_div_ceil_subadditive_guard :
    dm_target_div_ceil_subadditive :=
  fun T => ImportedDivMod.Prosa_Util_Div_mod_div_ceil_subadditive
    (sub_nat_to_imported T).

Definition exact_target_div_ceil_multiple_guard :
    dm_target_div_ceil_multiple :=
  fun delta T n => ImportedDivMod.Prosa_Util_Div_mod_div_ceil_multiple
    (sub_nat_to_imported delta) (sub_nat_to_imported T)
    (sub_nat_to_imported n).

Definition exact_target_div_floor_add_g_guard :
    dm_target_div_floor_add_g :=
  fun a b => ImportedDivMod.Prosa_Util_Div_mod_div_floor_add_g
    (sub_nat_to_imported a) (sub_nat_to_imported b).

Definition exact_target_mod_elim_guard : dm_target_mod_elim :=
  fun a b c => ImportedDivMod.Prosa_Util_Div_mod_mod_elim
    (sub_nat_to_imported a) (sub_nat_to_imported b)
    (sub_nat_to_imported c).

Print Assumptions exact_target_eqdivn_leqmodn_guard.
Print Assumptions exact_target_ltdivn_dvdn_guard.
Print Assumptions exact_target_addn1_modn_commute_guard.
Print Assumptions exact_target_addmod_le_mod_guard.
Print Assumptions exact_target_divn_leq_guard.
Print Assumptions exact_target_div_ceil0_guard.
Print Assumptions exact_target_div_ceil_gt0_guard.
Print Assumptions exact_target_div_ceil_monotone1_guard.
Print Assumptions exact_target_leq_div_ceil_add1_guard.
Print Assumptions exact_target_div_ceil_subadditive_guard.
Print Assumptions exact_target_div_ceil_multiple_guard.
Print Assumptions exact_target_div_floor_add_g_guard.
Print Assumptions exact_target_mod_elim_guard.
