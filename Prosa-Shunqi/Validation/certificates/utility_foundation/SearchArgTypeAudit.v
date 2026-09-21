From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchArg.

(** Exact compiled-target type guards.  Each definition below is accepted only
    if the displayed type is convertible to the type exported from the fresh
    [Prosa.Util.SearchArg] olean.  These guards are provenance evidence only;
    the semantic certificates do not import this module. *)

Definition search_arg_target_earliest_type_guard :
  forall (P : Lean.Nat -> ImportedSearchArg.Bool) (t1 t2 : Lean.Nat),
    Lean.Or
      (forall t : Lean.Nat,
        Lean.And
          (ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat t1 t)
          (ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat t t2) ->
        Lean.eq (P t) ImportedSearchArg.Bool_false)
      (ImportedSearchArg.Exists Lean.Nat (fun t =>
        Lean.And
          (Lean.And
            (ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat t1 t)
            (ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat t t2))
          (Lean.And
            (Lean.eq (P t) ImportedSearchArg.Bool_true)
            (forall t',
              ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat t1 t' ->
              Lean.eq (P t') ImportedSearchArg.Bool_true ->
              ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat t t')))) :=
  ImportedSearchArg.Prosa_Util_SearchArg_earliest_pred_element_exists_case.

Definition search_arg_target_none_type_guard :
  forall (T : Type) (f : Lean.Nat -> T)
      (P : T -> ImportedSearchArg.Bool)
      (R : T -> T -> ImportedSearchArg.Bool) (a b : Lean.Nat),
    ImportedSearchArg.Iff
      (Lean.eq (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T f P R a b)
        (ImportedSearchArg.Option_none_inst1 Lean.Nat))
      (forall x,
        Lean.And
          (ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat a x)
          (ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat x b) ->
        Lean.eq (P (f x)) ImportedSearchArg.Bool_false) :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg_none.

Definition search_arg_target_not_none_type_guard :
  forall (T : Type) (f : Lean.Nat -> T)
      (P : T -> ImportedSearchArg.Bool)
      (R : T -> T -> ImportedSearchArg.Bool) (a b : Lean.Nat),
    ImportedSearchArg.Exists Lean.Nat (fun x =>
      Lean.And
        (Lean.And
          (ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat a x)
          (ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat x b))
        (Lean.eq (P (f x)) ImportedSearchArg.Bool_true)) ->
    ImportedSearchArg.Exists Lean.Nat (fun y =>
      Lean.eq (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T f P R a b)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat y)) :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg_not_none.

Definition search_arg_target_pred_type_guard :
  forall (T : Type) (f : Lean.Nat -> T)
      (P : T -> ImportedSearchArg.Bool)
      (R : T -> T -> ImportedSearchArg.Bool) (a b x : Lean.Nat),
    Lean.eq (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T f P R a b)
      (ImportedSearchArg.Option_some_inst1 Lean.Nat x) ->
    Lean.eq (P (f x)) ImportedSearchArg.Bool_true :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg_pred.

Definition search_arg_target_in_range_type_guard :
  forall (T : Type) (f : Lean.Nat -> T)
      (P : T -> ImportedSearchArg.Bool)
      (R : T -> T -> ImportedSearchArg.Bool) (a b x : Lean.Nat),
    Lean.eq (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T f P R a b)
      (ImportedSearchArg.Option_some_inst1 Lean.Nat x) ->
    Lean.And
      (ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat a x)
      (ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat x b) :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg_in_range.

Definition search_arg_target_extremum_type_guard :
  forall (T : Type) (f : Lean.Nat -> T)
      (P : T -> ImportedSearchArg.Bool)
      (R : T -> T -> ImportedSearchArg.Bool),
    (forall x, Lean.eq (R x x) ImportedSearchArg.Bool_true) ->
    (forall x y z,
      Lean.eq (R x y) ImportedSearchArg.Bool_true ->
      Lean.eq (R y z) ImportedSearchArg.Bool_true ->
      Lean.eq (R x z) ImportedSearchArg.Bool_true) ->
    (forall x y,
      Lean.Or
        (Lean.eq (R x y) ImportedSearchArg.Bool_true)
        (Lean.eq (R y x) ImportedSearchArg.Bool_true)) ->
    forall a b x : Lean.Nat,
      Lean.eq (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T f P R a b)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat x) ->
      forall y : Lean.Nat,
        Lean.And
          (ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat a y)
          (ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat y b) ->
        Lean.eq (P (f y)) ImportedSearchArg.Bool_true ->
        Lean.eq (R (f x) (f y)) ImportedSearchArg.Bool_true :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg_extremum.

Definition search_arg_target_prop_on_ex_minn_type_guard :
  forall (P : Lean.Nat -> SProp)
      (pred : Lean.Nat -> ImportedSearchArg.Bool)
      (ex : ImportedSearchArg.Exists Lean.Nat
        (fun n => Lean.eq (pred n) ImportedSearchArg.Bool_true)),
    P (ImportedSearchArg.Nat_find
      (fun n => Lean.eq (pred n) ImportedSearchArg.Bool_true)
      (fun n => ImportedSearchArg.instDecidableEqBool
        (pred n) ImportedSearchArg.Bool_true) ex) ->
    ImportedSearchArg.Exists Lean.Nat (fun n =>
      Lean.And (P n)
        (Lean.And
          (Lean.eq (pred n) ImportedSearchArg.Bool_true)
          (forall n', Lean.eq (pred n') ImportedSearchArg.Bool_true ->
            ImportedSearchArg.LE_le_inst1 Lean.Nat
              ImportedSearchArg.instLENat n n'))) :=
  ImportedSearchArg.Prosa_Util_SearchArg_prop_on_ex_minn.
