import Prosa.Classic.Implementation.Global.Jitter.Schedule
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/implementation/global/jitter/schedule.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicImplGlobalJitterScheduleInterface

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



/-- Recursion equations of the structurally recursive `schedule_prefix` (kernel-checked, used as transport only). -/
theorem production_schedule_prefix_zero {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus) :
    Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction.schedule_prefix num_cpus build_schedule base_sched 0 = Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction.update_schedule num_cpus build_schedule base_sched 0 := rfl

theorem production_schedule_prefix_succ {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus) (n : Nat) :
    Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction.schedule_prefix num_cpus build_schedule base_sched (n + 1) =
      Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction.update_schedule num_cpus build_schedule (Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction.schedule_prefix num_cpus build_schedule base_sched n) (n + 1) := rfl
section McSortEqs
variable {T : Type u} (leT : T → T → Bool)
open Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler

/-- Defining equations of the restated MathComp `merge`/`merge_sort_*`/`sort` (kernel-checked `rfl`, transport only). -/
theorem xms_merge_nil (s2 : List T) : mc_merge leT [] s2 = s2 := rfl
theorem xms_merge_cons_nil (x1 : T) (s1 : List T) : mc_merge leT (x1 :: s1) [] = x1 :: s1 := rfl
theorem xms_merge_cons_cons (x1 : T) (s1 : List T) (x2 : T) (s2 : List T) :
    mc_merge leT (x1 :: s1) (x2 :: s2) =
      if leT x1 x2 then x1 :: mc_merge leT s1 (x2 :: s2) else x2 :: mc_merge leT (x1 :: s1) s2 := rfl
theorem xms_push_nil (s1 : List T) : mc_merge_sort_push leT s1 [] = [s1] := rfl
theorem xms_push_nil_cons (s1 : List T) (ss : List (List T)) : mc_merge_sort_push leT s1 ([] :: ss) = s1 :: ss := rfl
theorem xms_push_cons_cons (s1 : List T) (x : T) (s2 : List T) (ss : List (List T)) :
    mc_merge_sort_push leT s1 ((x :: s2) :: ss) = [] :: mc_merge_sort_push leT (mc_merge leT (x :: s2) s1) ss := rfl
theorem xms_pop_nil (s1 : List T) : mc_merge_sort_pop leT s1 [] = s1 := rfl
theorem xms_pop_cons (s1 s2 : List T) (ss : List (List T)) :
    mc_merge_sort_pop leT s1 (s2 :: ss) = mc_merge_sort_pop leT (mc_merge leT s2 s1) ss := rfl
theorem xms_rec_nil (ss : List (List T)) : mc_merge_sort_rec leT ss [] = mc_merge_sort_pop leT [] ss := rfl
theorem xms_rec_one (ss : List (List T)) (x : T) : mc_merge_sort_rec leT ss [x] = mc_merge_sort_pop leT [x] ss := rfl
theorem xms_rec_two (ss : List (List T)) (x1 x2 : T) (s : List T) :
    mc_merge_sort_rec leT ss (x1 :: x2 :: s) =
      mc_merge_sort_rec leT (mc_merge_sort_push leT (if leT x1 x2 then [x1, x2] else [x2, x1]) ss) s := rfl
theorem xms_sort (s : List T) : mc_sort leT s = mc_merge_sort_rec leT [] s := rfl

end McSortEqs

end Prosa.Validation.ClassicImplGlobalJitterScheduleInterface
