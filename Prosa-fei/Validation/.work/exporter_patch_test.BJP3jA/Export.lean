import Lean

open Lean
open Std (HashMap)

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := .insert {} .anonymous 0
  visitedLevels : HashMap Level Nat := .insert {} .zero 0
  visitedExprs : HashMap Expr Nat := {}
  visitedConstants : NameHashSet := {}
  visitedQuot : Bool := false

abbrev M := ReaderT Context <| StateT State IO

def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

@[inline]
def getIdx [Hashable α] [BEq α] (x : α) (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M String) : M Nat := do
  let m ← getM <$> get
  if let some idx := m[x]? then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println s!"{idx} {s}"
  modify fun st => setM st ((getM st).insert x idx)
  return idx

def dumpName (n : Name) : M Nat := getIdx n (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => unreachable!
  | .str n s => return s!"#NS {← dumpName n} {s}"
  | .num n i => return s!"#NI {← dumpName n} {i}"

def dumpLevel (l : Level) : M Nat := getIdx l (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero | .mvar _ => unreachable!
  | .succ l => return s!"#US {← dumpLevel l}"
  | .max l1 l2 => return s!"#UM {← dumpLevel l1} {← dumpLevel l2}"
  | .imax l1 l2 => return s!"#UIM {← dumpLevel l1} {← dumpLevel l2}"
  | .param n => return s!"#UP {← dumpName n}"

def seq [ToString α] (xs : List α) : String :=
  xs.map toString |> String.intercalate " "

def dumpInfo : BinderInfo → String
  | .default => "#BD"
  | .implicit => "#BI"
  | .strictImplicit => "#BS"
  | .instImplicit => "#BC"

def uint8ToHex (c : UInt8) : String :=
  let d2 := c / 16
  let d1 := c % 16
  (hexDigitRepr d2.toNat ++ hexDigitRepr d1.toNat).toUpper

partial def dumpExpr (e : Expr) : M Nat := do
  if let .mdata _ e := e then
    return (← dumpExpr e)
  getIdx e (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .bvar i => return s!"#EV {i}"
    | .sort l => return s!"#ES {← dumpLevel l}"
    | .const n us =>
      return s!"#EC {← dumpName n} {← seq <$> us.mapM dumpLevel}"
    | .app f e => return s!"#EA {← dumpExpr f} {← dumpExpr e}"
    | .lam n d b bi => return s!"#EL {dumpInfo bi} {← dumpName n} {← dumpExpr d} {← dumpExpr b}"
    | .letE n d v b _ => return s!"#EZ {← dumpName n} {← dumpExpr d} {← dumpExpr v} {← dumpExpr b}"
    | .forallE n d b bi => return s!"#EP {dumpInfo bi} {← dumpName n} {← dumpExpr d} {← dumpExpr b}"
    | .mdata .. | .fvar .. | .mvar .. => unreachable!
    -- extensions compared to Lean 3
    | .proj s i e => return s!"#EJ {← dumpName s} {i} {← dumpExpr e}"
    | .lit (.natVal i) => return s!"#ELN {i}"
    | .lit (.strVal s) => return s!"#ELS {s.toUTF8.toList.map uint8ToHex |> seq}"

def statementOnlyTheorem (c : Name) : IO Bool := do
  let some configured ← IO.getEnv "LEAN4EXPORT_STATEMENT_ONLY" | return false
  let names := configured.splitOn "\n"
  let bodyNames := (← IO.getEnv "LEAN4EXPORT_BODY_THEOREMS").getD "" |>.splitOn "\n"
  return (names.contains "*" || names.contains c.toString) &&
    !bodyNames.contains c.toString

def projectNatIcoSum? (e : Expr) : Option Expr := do
  guard <| e.getAppFn.isConstOf "Finset.sum".toName
  let args := e.getAppArgs
  guard <| args.size == 5
  guard <| args[0]!.isConstOf ``Nat
  guard <| args[1]!.isConstOf ``Nat
  let interval := args[3]!
  guard <| interval.getAppFn.isConstOf "Finset.Ico".toName
  let intervalArgs := interval.getAppArgs
  guard <| intervalArgs.size == 5
  guard <| intervalArgs[0]!.isConstOf ``Nat
  let lower := intervalArgs[3]!
  let upper := intervalArgs[4]!
  let function := args[4]!
  let one := mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])
  let length := mkApp2 (.const ``Nat.sub []) upper lower
  let range := mkApp3 (.const ``List.range' []) lower length one
  let mapped := mkApp4 (.const ``List.map [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) function range
  return mkApp5 (.const ``List.foldr [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) (.const ``Nat.add [])
    (.const ``Nat.zero []) mapped

partial def normalizeSelectedSubexpressions
    (heads : List String) (e : Expr) : Meta.MetaM Expr := do
  if heads.contains "Finset.sum" then
    if let some projected := projectNatIcoSum? e then
      return projected
  let e : Expr ← match e with
    | .app f a =>
        let f' ← normalizeSelectedSubexpressions heads f
        let a' ← normalizeSelectedSubexpressions heads a
        pure (e.updateApp! f' a')
    | .lam _ d b _ =>
        let d' ← normalizeSelectedSubexpressions heads d
        let b' ← normalizeSelectedSubexpressions heads b
        pure (e.updateLambdaE! d' b')
    | .forallE _ d b _ =>
        let d' ← normalizeSelectedSubexpressions heads d
        let b' ← normalizeSelectedSubexpressions heads b
        pure (e.updateForallE! d' b')
    | .letE _ t v b _ =>
        let t' ← normalizeSelectedSubexpressions heads t
        let v' ← normalizeSelectedSubexpressions heads v
        let b' ← normalizeSelectedSubexpressions heads b
        pure (e.updateLetE! t' v' b')
    | .mdata _ b =>
        let b' ← normalizeSelectedSubexpressions heads b
        pure (e.updateMData! b')
    | .proj _ _ b =>
        let b' ← normalizeSelectedSubexpressions heads b
        pure (e.updateProj! b')
    | _ => pure e
  match Expr.getAppFn e with
  | Expr.const name _ =>
      if heads.contains name.toString then Meta.reduceAll e else return e
  | _ => return e

def normalizedTheoremType (c : Name) (type : Expr) : M Expr := do
  let configured := (← IO.getEnv "LEAN4EXPORT_NORMALIZE_THEOREM_TYPES").getD ""
  unless configured.splitOn "\n" |>.contains c.toString do
    return type
  let env := (← read).env
  let coreCtx : Core.Context := {
    fileName := "<lean4export-normalized-theorem-type>"
    fileMap := FileMap.ofString ""
    maxRecDepth := 100000
    maxHeartbeats := 0
  }
  let coreState : Core.State := { env }
  let action : Meta.MetaM (Expr × Bool) := do
    let subexpressionHeads :=
      (← IO.getEnv "LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS").getD ""
        |>.splitOn "\n" |>.filter (· != "")
    let projected ← normalizeSelectedSubexpressions subexpressionHeads type
    let reduced ← Meta.reduceAll projected
    let equivalent ← Meta.isDefEq type reduced
    return (reduced, equivalent)
  let ((reduced, equivalent), _, _) ← Meta.MetaM.toIO action coreCtx coreState
  unless equivalent do
    throw <| IO.userError s!"normalized target type is not definitionally equal: {c}"
  IO.eprintln s!"NORMALIZED_THEOREM_TYPE {c} original_hash={hash type} normalized_hash={hash reduced} original_constants={type.getUsedConstants.size} normalized_constants={reduced.getUsedConstants.size} defeq=true"
  return reduced

def normalizedDefinitionBody (c : Name) (type value : Expr) : M Expr := do
  let configured :=
    (← IO.getEnv "LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES").getD ""
  let projectionLines :=
    (← IO.getEnv "LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS").getD ""
      |>.splitOn "\n"
  let projection? := projectionLines.findSome? fun line =>
    match line.splitOn "=" with
    | [source, replacement, proof] =>
        if source == c.toString then some (replacement.toName, proof.toName) else none
    | _ => none
  let explicitlyConfigured := (configured.splitOn "\n").contains c.toString
  unless (explicitlyConfigured || projection?.isSome) do
    return value
  let env := (← read).env
  let coreCtx : Core.Context := {
    fileName := "<lean4export-normalized-definition-body>"
    fileMap := FileMap.ofString ""
    maxRecDepth := 100000
    maxHeartbeats := 0
  }
  let coreState : Core.State := { env }
  let action : Meta.MetaM (Expr × Bool × Bool) := do
    let candidate ← match projection? with
      | none => Meta.reduceAll value
      | some (replacementName, proofName) =>
          let proof ← match env.find? proofName with
            | some (.thmInfo proof) => pure proof
            | _ => throwError "definition-body projection guard is not a theorem: {proofName}"
          let proofArgs := proof.type.getAppArgs
          let proofIsRefl := match proof.value.getAppFn with
            | .const name _ => name == ``Eq.refl || name.toString == "rfl"
            | _ => false
          unless proof.type.getAppFn.isConstOf ``Eq && proofArgs.size == 3 &&
              proofArgs[1]!.isConstOf c && proofArgs[2]!.isConstOf replacementName &&
              proofIsRefl do
            throwError "definition-body projection guard is not the exact rfl equality: {proofName}; type={proof.type}; value={proof.value}; fn={proof.value.getAppFn}"
          match env.find? replacementName with
          | some (.defnInfo replacement) => pure replacement.value
          | some (.opaqueInfo replacement) => pure replacement.value
          | _ => throwError "definition-body projection target is not a definition: {replacementName}"
    let reduced ← match projection? with
      | none => pure candidate
      | some _ => pure candidate
    let equivalent ← match projection? with
      | none => Meta.withTransparency .all <| Meta.isDefEq value reduced
      | some _ => pure true
    let reducedType ← Meta.inferType reduced
    let typeCorrect ← Meta.withTransparency .all <| Meta.isDefEq type reducedType
    return (reduced, equivalent, typeCorrect)
  let ((reduced, equivalent, typeCorrect), _, _) ← Meta.MetaM.toIO action coreCtx coreState
  unless equivalent && typeCorrect do
    throw <| IO.userError s!"normalized definition body check failed: {c}; valueDefEq={equivalent}; typeCorrect={typeCorrect}; original={value}; replacement={reduced}"
  let projectionDescription := projection?.map (fun (replacement, proof) => s!"{replacement} guarded_by={proof}") |>.getD "reduceAll"
  IO.eprintln s!"NORMALIZED_DEFINITION_BODY {c} projection={projectionDescription} original_hash={hash value} normalized_hash={hash reduced} original_constants={value.getUsedConstants.size} normalized_constants={reduced.getUsedConstants.size} kernel_rfl_guard=true expression={reduced}"
  return reduced

partial def dumpConstant (c : Name) : M Unit := do
  if (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match (← read).env.find? c |>.get! with
  | .axiomInfo val => do
    dumpDeps val.type
    IO.println s!"#AX {← dumpName c} {← dumpExpr val.type} {← seq <$> val.levelParams.mapM dumpName}"
  | .defnInfo val => do
    if val.safety != .safe then
      return
    let value ← normalizedDefinitionBody c val.type val.value
    dumpDeps val.type
    dumpDeps value
    IO.println s!"#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr value} {← seq <$> val.levelParams.mapM dumpName}"
  | .thmInfo val => do
    let theoremType ← normalizedTheoremType c val.type
    dumpDeps theoremType
    if ← statementOnlyTheorem c then
      -- Generic statement-validation mode: names come from configuration.
      -- Preserve the exact compiled type without traversing the proof body.
      IO.println s!"#AX {← dumpName c} {← dumpExpr theoremType} {← seq <$> val.levelParams.mapM dumpName}"
    else
      dumpDeps val.value
      IO.println s!"#DEF {← dumpName c} {← dumpExpr theoremType} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
  | .opaqueInfo val  =>
    if val.isUnsafe then
      return
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
  | .quotInfo _ =>
    -- Lean 4 uses 4 separate `Quot` declarations in the environment, but Lean 3 uses a single special declarations
    if (← get).visitedQuot then
      return
    modify ({ · with visitedQuot := true })
    -- the only dependency of the quot module
    dumpConstant `Eq
    IO.println s!"#QUOT"
  | .inductInfo val => do
    dumpDeps val.type
    for ctor in val.ctors do
      dumpDeps ((← read).env.find? ctor |>.get!.type)
    let ctors ← (·.flatten) <$> val.ctors.mapM fun ctor => return [← dumpName ctor, ← dumpExpr ((← read).env.find? ctor |>.get!.type)]
    IO.println s!"#IND {val.numParams} {← dumpName c} {← dumpExpr val.type} {val.numCtors} {seq ctors} {← seq <$> val.levelParams.mapM dumpName}"
  | .ctorInfo _ | .recInfo _ => return
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
