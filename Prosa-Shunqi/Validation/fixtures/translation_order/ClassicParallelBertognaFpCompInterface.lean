import Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/analysis/global/parallel/bertogna_fp_comp.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicParallelBertognaFpCompInterface

open Lean Elab Command Meta
open BigOperators


open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule

universe u

theorem finRange_map_shift (n : Nat) : ∀ s : Nat,
    (List.finRange n).map (fun i => s + i.val) = List.range' s n := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      rw [List.finRange_succ, List.map_cons, List.map_map, List.range'_succ]
      have h : ((fun i : Fin (n + 1) => s + i.val) ∘ (Fin.succ : Fin n → Fin (n + 1))) =
          (fun i : Fin n => (s + 1) + i.val) := by
        funext i
        show s + (i.val + 1) = s + 1 + i.val
        rw [Nat.add_assoc, Nat.add_comm i.val 1]
      rw [h, ih (s + 1)]
      rfl

theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  have h := finRange_map_shift n 0
  have e : (fun i : Fin n => 0 + i.val) = Fin.val := by
    funext i
    exact Nat.zero_add i.val
  rw [e] at h
  exact h

/-- `any` over all ordinals, read through `Fin.val`. -/
theorem finRange_any (n : Nat) (q : Fin n → Bool) :
    (List.finRange n).any q =
      (List.range' 0 n).any (fun k => if h : k < n then q ⟨k, h⟩ else false) := by
  rw [← finRange_map_val, List.any_map]
  congr 1
  funext i
  show q i = if h : i.val < n then q ⟨i.val, h⟩ else false
  rw [dif_pos i.isLt]

theorem map_finRange_eq_map_range' {α : Type u} (n : Nat) (f : Fin n → α) (d : α) :
    (List.finRange n).map f = (List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else d) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range']
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range', Nat.zero_add, Nat.one_mul,
      Fin.cast_mk, dif_pos h1]

theorem bigCatFin_range' {α : Type u} (n : Nat) (f : Fin n → List α) :
    Prosa.Util.Bigcat.bigCatFin f =
      ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else [])).flatten := by
  rw [← map_finRange_eq_map_range']
  unfold Prosa.Util.Bigcat.bigCatFin
  rw [List.ofFn_eq_map]

theorem fin_sum_range' (n : Nat) (f : Fin n → Nat) :
    (∑ i : Fin n, f i) =
      List.foldr Nat.add 0 ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0)) := by
  rw [← map_finRange_eq_map_range']
  rfl

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

/-- LEAN_HELPER (fixture): counting a filtered list as a sum of `if _ then 1 else 0`, by structural
recursion only (no arithmetic decision procedure in the proof). -/
theorem count_filter_eq {α : Type u} (p : α → Bool) :
    ∀ l : List α, List.foldr Nat.add 0 ((l.filter p).map (fun _ => 1)) =
      List.foldr Nat.add 0 (l.map (fun c => if p c = true then 1 else 0))
  | [] => rfl
  | a :: l => by
    cases h : p a
    · have e : (a :: l).filter p = l.filter p := by
        show (match p a with | true => a :: l.filter p | false => l.filter p) = l.filter p
        rw [h]
      rw [e, count_filter_eq p l]
      show List.foldr Nat.add 0 (l.map (fun c => if p c = true then 1 else 0)) =
        Nat.add (if p a = true then 1 else 0) (List.foldr Nat.add 0 (l.map (fun c => if p c = true then 1 else 0)))
      rw [h]
      exact (Nat.zero_add _).symm
    · have e : (a :: l).filter p = a :: l.filter p := by
        show (match p a with | true => a :: l.filter p | false => l.filter p) = a :: l.filter p
        rw [h]
      rw [e]
      show Nat.add 1 (List.foldr Nat.add 0 ((l.filter p).map (fun _ => 1))) =
        Nat.add (if p a = true then 1 else 0) (List.foldr Nat.add 0 (l.map (fun c => if p c = true then 1 else 0)))
      rw [h, count_filter_eq p l]
      rfl

theorem service_at_sum {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) :
    service_at sched j t = ∑ cpu : Fin num_cpus, (if scheduled_on sched j cpu t = true then 1 else 0) := by
  show List.foldr Nat.add 0
      (((List.finRange num_cpus).filter (fun cpu => decide (scheduled_on sched j cpu t = true))).map (fun _ => 1)) =
    List.foldr Nat.add 0 ((List.finRange num_cpus).map (fun cpu => if scheduled_on sched j cpu t = true then 1 else 0))
  rw [count_filter_eq]
  congr 2
  funext c
  cases scheduled_on sched j c t <;> rfl

theorem dedup_nil {α : Type u} [DecidableEq α] : ([] : List α).dedup = [] := List.dedup_nil

theorem dedup_cons_mem {α : Type u} [DecidableEq α] (a : α) (l : List α) (h : a ∈ l) :
    (a :: l).dedup = l.dedup := List.dedup_cons_of_mem h

theorem dedup_cons_not_mem {α : Type u} [DecidableEq α] (a : α) (l : List α) (h : ¬ a ∈ l) :
    (a :: l).dedup = a :: l.dedup := List.dedup_cons_of_notMem h

universe v

/-- Body projections of the global interference definitions (half-open `Finset.Ico` sums as list folds). -/
def total_interference_proj {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (backlogged job_arrival job_cost sched j t).toNat)
      (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem total_interference_proj_guard : @Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.total_interference = @total_interference_proj := rfl

def job_interference_proj {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j job_other : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => ∑ cpu : Fin num_cpus,
        (backlogged job_arrival job_cost sched j t && scheduled_on sched job_other cpu t).toNat)
      (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem job_interference_proj_guard : @Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.job_interference = @job_interference_proj := rfl

def task_interference_proj {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (tsk_other : sporadic_task) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => ∑ cpu : Fin num_cpus,
        (backlogged job_arrival job_cost sched j t &&
          Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.task_scheduled_on job_task sched tsk_other cpu t).toNat)
      (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem task_interference_proj_guard : @Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference.task_interference = @task_interference_proj := rfl

def service_proj {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t' : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => service_at sched j t) (List.range' 0 (Nat.sub t' 0) (Nat.succ Nat.zero)))

theorem service_proj_guard : @service = @service_proj := rfl

def service_during_proj {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => service_at sched j t) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem service_during_proj_guard : @service_during = @service_during_proj := rfl

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




theorem xfc_iter_zero (f : Nat → Nat) (x : Nat) : Prosa.Classic.Util.Fixedpoint.iter 0 f x = x := rfl
theorem xfc_iter_succ (f : Nat → Nat) (n x : Nat) :
    Prosa.Classic.Util.Fixedpoint.iter (n + 1) f x = f (Prosa.Classic.Util.Fixedpoint.iter n f x) := rfl
theorem xfc_bound_none {T : Type u} [DecidableEq T] (tc tp td : T → Prosa.Classic.Model.Time.Time.time) (m : Nat) (tsk : T) :
    Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp.ResponseTimeIterationFP.fp_bound_of_task tc tp td m none tsk = none := rfl
theorem xfc_bound_some {T : Type u} [DecidableEq T] (tc tp td : T → Prosa.Classic.Model.Time.Time.time) (m : Nat)
    (rt : List (T × Prosa.Classic.Model.Time.Time.time)) (tsk : T) :
    Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp.ResponseTimeIterationFP.fp_bound_of_task tc tp td m (some rt) tsk =
      (if Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp.ResponseTimeIterationFP.per_task_rta tc tp m tsk rt (Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp.ResponseTimeIterationFP.max_steps tc td tsk) ≤ td tsk then
        some (rt ++ [(tsk, Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp.ResponseTimeIterationFP.per_task_rta tc tp m tsk rt (Prosa.Classic.Analysis.Global.Parallel.BertognaFpComp.ResponseTimeIterationFP.max_steps tc td tsk))]) else none) := rfl

end Prosa.Validation.ClassicParallelBertognaFpCompInterface

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
