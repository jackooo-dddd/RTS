import Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/model/schedule/uni/limited/edf/response_time_bound.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicLimitedEdfRtaInterface

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

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

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

universe v

/-- Body projections of the half-open `Finset.Ico` sums (as list folds). -/
def cumul_interference_proj {Job : Type v} [DecidableEq Job] (interference : Job → time → Bool) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (interference j t).toNat) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem cumul_interference_proj_guard : @Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions.cumul_interference = @cumul_interference_proj := rfl

def cumul_interfering_workload_proj {Job : Type v} [DecidableEq Job] (interfering_workload : Job → time → time)
    (j : Job) (t1 t2 : Nat) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => interfering_workload j t) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem cumul_interfering_workload_proj_guard : @Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions.cumul_interfering_workload = @cumul_interfering_workload_proj := rfl

def cumul_task_interference_proj {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task)
    (arr_seq : Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence.arrival_sequence Job) (sched : schedule Job)
    (interference : Job → time → Bool) (tsk : Task) (upper_bound : time) (t1 t2 : Nat) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA.task_interference_received_before job_task arr_seq sched interference tsk upper_bound t).toNat)
      (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem cumul_task_interference_proj_guard : @Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA.cumul_task_interference = @cumul_task_interference_proj := rfl

/-- Body projection of `cumulative_priority_inversion` (the half-open `Finset.Ico` sum as a list fold). -/
def cumulative_priority_inversion_proj {Job : Type v} [DecidableEq Job] (sched : schedule Job)
    (higher_eq_priority : Prosa.Classic.Model.Priority.Priority.JLFP_policy Job) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j t).toNat)
      (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem cumulative_priority_inversion_proj_guard :
    @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.cumulative_priority_inversion = @cumulative_priority_inversion_proj := rfl

end Prosa.Validation.ClassicLimitedEdfRtaInterface
