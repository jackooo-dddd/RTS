import Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/implementation/uni/basic/extraction_tdma.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicExtractionTdmaInterface

open Lean Elab Command Meta

open Prosa.Classic.Model.Time.Time

open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u

open Prosa.Util.Sum

theorem production_sumSeq_nil {X : Type u} (F : X → Nat) : sumSeq [] F = 0 := rfl

theorem production_sumSeq_cons {X : Type u} (F : X → Nat) (x : X) (xs : List X) :
    sumSeq (x :: xs) F = F x + sumSeq xs F := by
  simp [sumSeq]

theorem production_sumFiltered_nil {X : Type u} (P : X → Bool) (F : X → Nat) :
    sumFiltered [] P F = 0 := rfl

theorem production_sumFiltered_cons_true {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = true) :
    sumFiltered (x :: xs) P F = F x + sumFiltered xs P F := by
  simp [sumFiltered, h]

theorem production_sumFiltered_cons_false {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = false) :
    sumFiltered (x :: xs) P F = sumFiltered xs P F := by
  simp [sumFiltered, h]

def service_during_proj {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => service_at sched j t) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem service_during_proj_guard : @service_during = @service_during_proj := rfl

def total_service_during_proj {Job : Type u} [DecidableEq Job] (sched : schedule Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (!is_idle sched t).toNat) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem total_service_during_proj_guard : @total_service_during = @total_service_during_proj := rfl

/-- The index types of projected sums: `Nat` and the reducible alias `time` (the exporter's opt-in
`LEAN4EXPORT_NAT_INDEX_ALIASES` list for this export, `export_env` of the spec). -/
private def natIndexType (t : Expr) : Bool :=
  t.isConstOf ``Nat || t.isConstOf ``Prosa.Classic.Model.Time.Time.time

private def projectNatIcoSum? (e : Expr) : Option Expr := do
  guard <| e.getAppFn.isConstOf ``Finset.sum
  let args := e.getAppArgs
  guard <| args.size == 5
  guard <| natIndexType args[0]!
  guard <| args[1]!.isConstOf ``Nat
  let (interval, filt?) :=
    if args[3]!.getAppFn.isConstOf ``Finset.filter && args[3]!.getAppArgs.size == 4 then
      (args[3]!.getAppArgs[3]!, some (args[3]!.getAppArgs[1]!, args[3]!.getAppArgs[2]!))
    else (args[3]!, none)
  guard <| interval.getAppFn.isConstOf ``Finset.Ico
  let intervalArgs := interval.getAppArgs
  guard <| intervalArgs.size == 5
  guard <| natIndexType intervalArgs[0]!
  let lower := intervalArgs[3]!
  let upper := intervalArgs[4]!
  let function := args[4]!
  let one := mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])
  let length := mkApp2 (.const ``Nat.sub []) upper lower
  let range0 := mkApp3 (.const ``List.range' []) lower length one
  let range := match filt? with
    | none => range0
    | some (p, dec) =>
        let decideFn := Expr.lam `i (.const ``Nat [])
          (mkApp2 (.const ``Decidable.decide []) (.app (p.liftLooseBVars 0 1) (.bvar 0))
            (.app (dec.liftLooseBVars 0 1) (.bvar 0))) .default
        mkApp3 (.const ``List.filter [.zero]) (.const ``Nat []) decideFn range0
  let mapped := mkApp4 (.const ``List.map [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) function range
  return mkApp5 (.const ``List.foldr [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) (.const ``Nat.add [])
    (.const ``Nat.zero []) mapped

private partial def projectSums (e : Expr) : MetaM Expr := do
  if let some projected := projectNatIcoSum? e then
    return projected
  match e with
  | .app f a => return e.updateApp! (← projectSums f) (← projectSums a)
  | .lam _ d b _ => return e.updateLambdaE! (← projectSums d) (← projectSums b)
  | .forallE _ d b _ => return e.updateForallE! (← projectSums d) (← projectSums b)
  | .letE _ t v b _ =>
      return e.updateLetE! (← projectSums t) (← projectSums v)
        (← projectSums b)
  | .mdata _ b => return e.updateMData! (← projectSums b)
  | .proj _ _ b => return e.updateProj! (← projectSums b)
  | _ => return e

private def addNormalizationGuard (target guard : Name) : MetaM Unit := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? target
    | throwError "normalization target is not a theorem: {target}"
  let normalized ← projectSums info.type
  unless ← Meta.isDefEq info.type normalized do
    logInfo m!"NORMALIZATION_MISMATCH target={target} original={info.type} normalized={normalized}"
    throwError "normalization is not definitionally equal: {target}"
  let guardType ← Meta.mkEq info.type normalized
  let guardValue ← Meta.mkEqRefl info.type
  addDecl <| .thmDecl {
    name := guard
    levelParams := info.levelParams
    type := guardType
    value := guardValue
  }
  logInfo m!"KERNEL_NORMALIZATION_GUARD target={target} guard={guard} original_hash={hash info.type} normalized_hash={hash normalized} proof=Eq.refl"
open Prosa.Classic.Model.Schedule.Uni.EndTime.end_time

theorem end_time_option_c0 {Job : Type u} [DecidableEq Job] (sched : schedule Job) (job : Job) (t : time) (wf : Nat) :
    end_time_option sched job t 0 wf = diagnosis_option.OK t := by cases wf <;> rfl
theorem end_time_option_wf0 {Job : Type u} [DecidableEq Job] (sched : schedule Job) (job : Job) (t : time) (c : Nat) :
    end_time_option sched job t (c + 1) 0 = diagnosis_option.Failure t := rfl
theorem end_time_option_step {Job : Type u} [DecidableEq Job] (sched : schedule Job) (job : Job) (t : time) (c wf : Nat) :
    end_time_option sched job t (c + 1) (wf + 1) =
      bif scheduled_at sched job t then end_time_option sched job (t + 1) c wf
      else end_time_option sched job (t + 1) (c + 1) wf := by
  show (if scheduled_at sched job t then _ else _) = _
  cases scheduled_at sched job t <;> rfl


open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_get_slot_eq (a b c d : Nat) : get_slot (Task_T.build_task a b c d) = a := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_get_cost_eq (a b c d : Nat) : get_cost (Task_T.build_task a b c d) = b := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_get_D_eq (a b c d : Nat) : get_D (Task_T.build_task a b c d) = c := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_get_P_eq (a b c d : Nat) : get_P (Task_T.build_task a b c d) = d := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_In_nil (a : Task_T) : In a [] = False := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_In_cons (a b : Task_T) (m : List Task_T) : In a (b :: m) = (a = b ∨ In a m) := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_test_nil (T : Nat) : schedulability_test T [] = true := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_test_cons (T : Nat) (x : Task_T) (s : List Task_T) :
    schedulability_test T (x :: s) = (schedulable_tsk T x && schedulability_test T s) := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_cycle_nil : cycle [] = 0 := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
theorem xt_cycle_cons (x : Task_T) (l : List Task_T) : cycle (x :: l) = get_slot x + cycle l := rfl
open Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma in
open Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA in
theorem xt_schedulable_tsk_eq (T : Nat) (tsk : Task_T) :
    schedulable_tsk T tsk =
      (decide (WCRT_formula T (get_slot tsk) (get_cost tsk) ≤ get_D tsk) &&
       decide (WCRT_formula T (get_slot tsk) (get_cost tsk) ≤ get_P tsk)) := by
  unfold schedulable_tsk
  show (if (_ : Bool) = true then true else false) = _
  cases decide (WCRT_formula T (get_slot tsk) (get_cost tsk) ≤ get_D tsk) &&
    decide (WCRT_formula T (get_slot tsk) (get_cost tsk) ≤ get_P tsk) <;> rfl

end Prosa.Validation.ClassicExtractionTdmaInterface

namespace Prosa.Validation.DivModInterface

open Prosa.Classic.Util.DivMod

/-- Bind the validation interface to the actual production definitions. -/
theorem production_div_floor_eq (x y : Nat) :
    div_floor x y = x / y := rfl

theorem production_div_ceil_eq (x y : Nat) :
    div_ceil x y = if y ∣ x then x / y else x / y + 1 := rfl

/-- Euclidean computation facts for the exact target `Nat.div`/`Nat.mod`. -/
theorem production_div_add_mod (x y : Nat) :
    y * (x / y) + x % y = x := Nat.div_add_mod x y

theorem production_mod_lt (x y : Nat) (hy : 0 < y) :
    x % y < y := Nat.mod_lt x hy

theorem production_div_zero (x : Nat) : x / 0 = 0 := Nat.div_zero x

theorem production_mod_zero (x : Nat) : x % 0 = x := Nat.mod_zero x

theorem production_dvd_iff_mod_eq_zero (x y : Nat) :
    y ∣ x ↔ x % y = 0 := Nat.dvd_iff_mod_eq_zero

end Prosa.Validation.DivModInterface
