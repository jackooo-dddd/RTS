import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/model/schedule/uni/limited/platform/limited.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicLimitedModelInterface

open Lean Elab Command Meta

open Prosa.Classic.Model.Time.Time

open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u

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

open Prosa.Util.List Prosa.Util.Nondecreasing

theorem distances_nil : distances [] = [] := rfl
theorem distances_single (x : Nat) : distances [x] = [] := rfl
theorem distances_cons2 (x y : Nat) (ys : List Nat) : distances (x :: y :: ys) = (y - x) :: distances (y :: ys) := rfl
theorem max0_eq (xs : List Nat) : max0 xs = List.foldl Nat.max 0 xs := rfl
theorem foldl_max_nil (z : Nat) : List.foldl Nat.max z [] = z := rfl
theorem foldl_max_cons (z x : Nat) (xs : List Nat) : List.foldl Nat.max z (x :: xs) = List.foldl Nat.max (Nat.max z x) xs := rfl
theorem first0_nil : first0 [] = 0 := rfl
theorem first0_cons (x : Nat) (xs : List Nat) : first0 (x :: xs) = x := rfl
theorem last0_nil : last0 [] = 0 := rfl
theorem last0_single (x : Nat) : last0 [x] = x := rfl
theorem last0_cons2 (x y : Nat) (ys : List Nat) : last0 (x :: y :: ys) = last0 (y :: ys) := rfl
theorem getD_nil (n d : Nat) : ([] : List Nat).getD n d = d := rfl
theorem getD_cons_zero (x : Nat) (xs : List Nat) (d : Nat) : (x :: xs).getD 0 d = x := rfl
theorem getD_cons_succ (x : Nat) (xs : List Nat) (n d : Nat) : (x :: xs).getD (n + 1) d = xs.getD n d := rfl
theorem length_nil : ([] : List Nat).length = 0 := rfl
theorem length_cons (x : Nat) (xs : List Nat) : (x :: xs).length = xs.length + 1 := rfl
theorem nondecreasing_sequence_eq (xs : List Nat) :
    nondecreasing_sequence xs = (∀ n1 n2, n1 ≤ n2 ∧ n2 < xs.length → xs.getD n1 0 ≤ xs.getD n2 0) := rfl

end Prosa.Validation.ClassicLimitedModelInterface
