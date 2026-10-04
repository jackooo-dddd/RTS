import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.MainClaim
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/analysis/uni/susp/sustainability/allcosts/main_claim.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicAllcostsMainInterface

open Lean Elab Command Meta

open Prosa.Classic.Model.Time.Time

open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

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

theorem maxFiltered_eq_foldr_cond {I : Type u} (P : I → Bool) (F : I → Nat) :
    ∀ r : List I, Prosa.Util.Sum.maxFiltered r P F = List.foldr Nat.max 0 (r.map (fun x => bif P x then F x else 0))
  | [] => rfl
  | x :: xs => by
    have ih := maxFiltered_eq_foldr_cond P F xs
    cases h : P x
    · show List.foldr max 0 (List.map F (List.filter P (x :: xs))) = Nat.max (bif P x then F x else 0) _
      rw [List.filter_cons_of_neg (by simp [h])]
      rw [h]
      show Prosa.Util.Sum.maxFiltered xs P F = Nat.max 0 _
      rw [ih]
      exact (Nat.zero_max _).symm
    · show List.foldr max 0 (List.map F (List.filter P (x :: xs))) = Nat.max (bif P x then F x else 0) _
      rw [List.filter_cons_of_pos h, h]
      show max (F x) (Prosa.Util.Sum.maxFiltered xs P F) = Nat.max (F x) _
      rw [ih]

theorem maxFiltered_finRange (n : Nat) (P : Fin n → Bool) (F : Fin n → Nat) :
    Prosa.Util.Sum.maxFiltered (List.finRange n) P F =
      List.foldr Nat.max 0 ((List.range' 0 n).map
        (fun k => if h : k < n then (bif P ⟨k, h⟩ then F ⟨k, h⟩ else 0) else 0)) := by
  rw [maxFiltered_eq_foldr_cond, map_finRange_eq_map_range' n (fun x => bif P x then F x else 0) 0]

def service_during_proj {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => service_at sched j t) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem service_during_proj_guard : @service_during = @service_during_proj := rfl

def total_service_during_proj {Job : Type u} [DecidableEq Job] (sched : schedule Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (!is_idle sched t).toNat) (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem total_service_during_proj_guard : @total_service_during = @total_service_during_proj := rfl

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

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

open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals

universe v

def total_suspension_proj {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (next_suspension : job_suspension Job) (j : Job) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => next_suspension j t) (List.range' 0 (Nat.sub (job_cost j) 0) (Nat.succ Nat.zero)))

theorem total_suspension_proj_guard : @total_suspension = @total_suspension_proj := rfl

def cumulative_suspension_during_proj {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t1 t2 : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (suspended_at job_arrival job_cost next_suspension sched j t).toNat)
      (List.range' t1 (Nat.sub t2 t1) (Nat.succ Nat.zero)))

theorem cumulative_suspension_during_proj_guard : @cumulative_suspension_during = @cumulative_suspension_during_proj := rfl

/-- Body projection of `build_suspension_duration` (the filtered half-open `Finset.Ico` sum as a list fold). -/
def build_suspension_duration_proj {Job : Type v} [DecidableEq Job] (sched : schedule Job) (t_max : time)
    (job_suspended_at : Job → time → Bool) (j : Job) (s : time) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => (job_suspended_at j t).toNat)
      (List.filter (fun t => decide (service sched j t = s)) (List.range' 0 (Nat.sub t_max 0) (Nat.succ Nat.zero))))

theorem build_suspension_duration_proj_guard : @Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable.SuspensionTableConstruction.build_suspension_duration = @build_suspension_duration_proj := rfl

/-- Recursion equations of the structurally recursive `schedule_prefix` (kernel-checked, used as transport only). -/
theorem production_schedule_prefix_zero {Job : Type u} [DecidableEq Job] (build_schedule : schedule Job → time → Option Job)
    (base_sched : schedule Job) :
    Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction.schedule_prefix build_schedule base_sched 0 = Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction.update_schedule build_schedule base_sched 0 := rfl

theorem production_schedule_prefix_succ {Job : Type u} [DecidableEq Job] (build_schedule : schedule Job → time → Option Job)
    (base_sched : schedule Job) (n : Nat) :
    Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction.schedule_prefix build_schedule base_sched (n + 1) =
      Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction.update_schedule build_schedule (Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction.schedule_prefix build_schedule base_sched n) (n + 1) := rfl

open Prosa.Classic.Model.Schedule.Uni.Sustainability.Sustainability


/-- `find_param` on the empty list and on a cons cell (kernel-checked; used by the Rocq certificate as
propositional equations only). -/
theorem xsu_find_param_nil {Job : Type u} [DecidableEq Job] (l : parameter_label) :
    find_param (Job := Job) l [] = job_parameter.param l (default_val l) := rfl

theorem xsu_find_param_cons {Job : Type u} [DecidableEq Job] (l : parameter_label) (p0 : job_parameter Job)
    (s : List (job_parameter Job)) :
    find_param l (p0 :: s) = if p0.p_label = l then p0 else find_param l s := by
  unfold find_param
  rw [List.findIdx_cons]
  by_cases h : p0.p_label = l
  · rw [if_pos h]
    have hd : decide (p0.p_label = l) = true := decide_eq_true h
    show List.getD (p0 :: s) (cond (decide (p0.p_label = l)) 0 _) _ = p0
    rw [hd]; rfl
  · rw [if_neg h]
    have hd : decide (p0.p_label = l) = false := decide_eq_false h
    show List.getD (p0 :: s) (cond (decide (p0.p_label = l)) 0 _) _ = _
    rw [hd]; rfl

/-- `get_param_function` on a parameter with the requested label, resp. with another label. -/
theorem xsu_get_param_same {Job : Type u} [DecidableEq Job] (l : parameter_label) (f : type_of_label (Job := Job) l) :
    get_param_function l (job_parameter.param l f) = f := by
  cases l <;> rfl

theorem xsu_get_param_other {Job : Type u} [DecidableEq Job] (l l' : parameter_label) (f : type_of_label (Job := Job) l')
    (h : l' ≠ l) : get_param_function l (job_parameter.param l' f) = default_val l := by
  cases l <;> cases l' <;> first | rfl | exact absurd rfl h

end Prosa.Validation.ClassicAllcostsMainInterface
