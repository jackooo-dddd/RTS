import { describe, expect, test } from "bun:test"
import fs from "fs"
import path from "path"
import { LeanGate } from "../../src/tool/lean-gate"
import { LeanSource } from "../../src/tool/lean-source"

const SOLUTION = `import CaseStudies.ECRTS2005.Lemma3.Statement

/-!
Benchmark task: prove the statement. Do not use \`sorry\` in the final proof.
-/

set_option linter.unusedVariables false

namespace CaseStudies.ECRTS2005.Lemma3

open CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF

universe u v

theorem solution : Lemma3_05_statement.{u, v} := by
  sorry

end CaseStudies.ECRTS2005.Lemma3
`

const withProof = (proof: string) => SOLUTION.replace("  sorry\n", proof)

describe("LeanSource", () => {
  test("strips nested block, doc and line comments like check.py", () => {
    const text = "a /- x /- y -/ z -/ b -- c\n/-- doc sorry -/ d"
    expect(LeanSource.stripComments(text)).toBe("a  b \n d")
  })

  test("finds forbidden tokens outside comments only", () => {
    expect(LeanSource.forbiddenTokens(SOLUTION)).toEqual(["sorry"])
    expect(LeanSource.forbiddenTokens(withProof("  exact foo -- sorry\n"))).toEqual([])
    expect(LeanSource.forbiddenTokens("axiom x : False\n#eval 1\nrun_cmd pure ()")).toEqual(["#eval", "axiom", "run_cmd"])
    expect(LeanSource.forbiddenTokens("set_option debug.skipKernelTC true")).toEqual(["set_option debug.", "skipKernelTC"])
    expect(LeanSource.forbiddenTokens(SOLUTION, ["sorry"])).toEqual([])
    // identifiers that merely contain a forbidden word are fine
    expect(LeanSource.forbiddenTokens("theorem sorry_free : True := trivial\nexact elaborate")).toEqual([])
  })

  test("keeps the token list identical to benchmark/check.py", () => {
    const checkPy = path.resolve(import.meta.dir, "../../../../../../Deliverables/lean-prosa-v06/benchmark/check.py")
    if (!fs.existsSync(checkPy)) return
    const text = fs.readFileSync(checkPy, "utf8")
    const block = /FORBIDDEN = \[([\s\S]*?)\]\n/.exec(text)![1]
    const python = [...block.matchAll(/r"((?:[^"\\]|\\.)*)"/g)].map((m) => m[1])
    expect(LeanSource.FORBIDDEN.map((re) => re.source)).toEqual(python)
    const allowed = /ALLOWED_AXIOMS = \{([^}]*)\}/.exec(text)![1]
    expect([...allowed.matchAll(/"([^"]+)"/g)].map((m) => m[1]).sort()).toEqual([...LeanSource.ALLOWED_AXIOMS].sort())
  })

  test("reads the import header and the body offset", () => {
    const header = LeanSource.header(SOLUTION)
    expect(header.imports).toEqual(["CaseStudies.ECRTS2005.Lemma3.Statement"])
    expect(header.bodyLine).toBe(1)
    expect(SOLUTION.slice(header.bodyOffset).startsWith("\n/-!")).toBe(true)
    const multi = LeanSource.header("-- c\nimport A.B C -- trailing\nimport D\n\ndef x := 1\n")
    expect(multi.imports).toEqual(["A.B", "C", "D"])
    expect(LeanSource.header("def x := 1\n").imports).toEqual([])
  })

  test("locates top-level declarations and their proofs", () => {
    const decl = LeanSource.findDeclaration(SOLUTION, "CaseStudies.ECRTS2005.Lemma3.solution")!
    expect(decl.name).toBe("solution")
    expect(decl.signature).toBe(": Lemma3_05_statement.{u, v}")
    expect(SOLUTION.slice(decl.assign!, decl.end)).toBe(":= by\n  sorry\n\n")
    const src = "theorem t {α : Type} (x : α) (h : x = x := rfl) : x = x := by\n  exact h\n@[simp] lemma l : True := trivial\n"
    expect(LeanSource.declarations(src).map((d) => d.name)).toEqual(["t", "l"])
    expect(LeanSource.findDeclaration(src, "t")!.signature).toBe("{α : Type} (x : α) (h : x = x := rfl) : x = x")
  })
})

describe("LeanGate exterior check (submission stage)", () => {
  const theorem = "solution"

  test("accepts a change inside the proof", () => {
    expect(LeanGate.exteriorChanges(SOLUTION, withProof("  intro h\n  exact h\n"), theorem)).toEqual([])
  })

  test("accepts added imports of package modules (K1) and rejects others", () => {
    const added = SOLUTION.replace(
      "import CaseStudies.ECRTS2005.Lemma3.Statement\n",
      "import CaseStudies.ECRTS2005.Lemma3.Statement\nimport Prosa.Util.Sum\nimport Mathlib.Tactic.Linarith\nimport CaseStudies.Support.Common\n",
    )
    expect(LeanGate.exteriorChanges(SOLUTION, added, theorem)).toEqual([])
    const foreign = SOLUTION.replace("import CaseStudies.ECRTS2005.Lemma3.Statement\n", "import CaseStudies.ECRTS2005.Lemma3.Statement\nimport Lean\n")
    expect(LeanGate.exteriorChanges(SOLUTION, foreign, theorem).map((r) => r.code)).toEqual(["IMPORT_NOT_ALLOWED"])
    const removed = SOLUTION.replace("import CaseStudies.ECRTS2005.Lemma3.Statement\n", "")
    expect(LeanGate.exteriorChanges(SOLUTION, removed, theorem).map((r) => r.code)).toContain("IMPORT_REMOVED")
  })

  test("rejects a changed statement and edits before or after the proof", () => {
    const statement = SOLUTION.replace("theorem solution : Lemma3_05_statement.{u, v}", "theorem solution : True")
    expect(LeanGate.exteriorChanges(SOLUTION, statement, theorem).map((r) => r.code)).toEqual(["REGION_OUTSIDE_EDIT"])
    const before = SOLUTION.replace("universe u v\n", "universe u v\n\ntheorem helper : True := trivial\n")
    expect(LeanGate.exteriorChanges(SOLUTION, before, theorem).map((r) => r.code)).toEqual(["REGION_OUTSIDE_EDIT"])
    const after = SOLUTION.replace("end CaseStudies.ECRTS2005.Lemma3\n", "end CaseStudies.ECRTS2005.Lemma3\n\ntheorem extra : True := trivial\n")
    expect(LeanGate.exteriorChanges(SOLUTION, after, theorem).map((r) => r.code)).toEqual(["REGION_OUTSIDE_EDIT"])
  })
})

describe("LeanGate helpers", () => {
  test("maps every check.py FAIL detail to a reason code", () => {
    const cases: [string, string][] = [
      ["read-only files were changed or added: modified: Prosa/Util/Sum.lean", "FROZEN_CHANGED"],
      ["solution file missing", "SOLUTION_MISSING"],
      ["forbidden token(s) in CaseStudies/X/Solution.lean: sorry", "FORBIDDEN_TOKEN"],
      ["build failed (timeout)", "BUILD_TIMEOUT"],
      ["build failed: error: unknown identifier", "BUILD_FAILED"],
      ["the solution does not prove the frozen statement: type mismatch", "STATEMENT_MISMATCH"],
      ["could not read the axioms: ...", "AXIOMS_UNREADABLE"],
      ["uses non-standard axioms: Lean.ofReduceBool", "AXIOMS"],
    ]
    for (const [detail, code] of cases) expect(LeanGate.checkPyReasonCode(detail)).toBe(code)
  })

  test("parses #print axioms output", () => {
    expect(LeanGate.parseAxioms("'x' does not depend on any axioms")).toEqual([])
    expect(LeanGate.parseAxioms("'x' depends on axioms: [propext,\n Classical.choice, Quot.sound]")).toEqual([
      "propext",
      "Classical.choice",
      "Quot.sound",
    ])
    expect(LeanGate.parseAxioms("error: unknown constant")).toBeUndefined()
  })

  test("turns a declaration signature into its type", () => {
    expect(LeanGate.binderSignatureAsType(": P")).toBe("P")
    expect(LeanGate.binderSignatureAsType("{α : Type} (x : α) : x = x")).toBe("∀ {α : Type} (x : α), x = x")
    expect(LeanGate.binderSignatureAsType("(h : a = b) : f (a : Nat) = f b")).toBe("∀ (h : a = b), f (a : Nat) = f b")
  })
})

/**
 * Integration (needs a built copy of lean-prosa-v06 staged per DECISIONS D14 and the reference solutions):
 *   PROSABUDDY_LEAN_INTEGRATION=1 LEANBUDDY_TEST_PACKAGE=<run copy> LEANBUDDY_TEST_REFERENCES=<reference solutions>
 */
const integration = process.env.PROSABUDDY_LEAN_INTEGRATION === "1" && process.env.LEANBUDDY_TEST_PACKAGE
describe.skipIf(!integration)("LeanGate integration (built package)", () => {
  const root = process.env.LEANBUDDY_TEST_PACKAGE!
  const refs = process.env.LEANBUDDY_TEST_REFERENCES ?? ""
  const rel = "CaseStudies/ECRTS2005/Lemma3/Solution.lean"
  const file = path.join(root ?? "", rel)
  const run = (candidate: string, stage: LeanGate.Stage = "final", allowSorry = false) =>
    LeanGate.run({ file, theorem: "solution", baselineSource: fs.readFileSync(file, "utf8"), candidateSource: candidate, stage, allowSorry })

  test(
    "final gate on the reference solution (candidate path) accepts with the standard axioms only",
    async () => {
      fs.mkdirSync(path.join(root, "CaseStudies/Support"), { recursive: true })
      for (const f of fs.readdirSync(path.join(refs, "CaseStudies/Support"))) {
        fs.copyFileSync(path.join(refs, "CaseStudies/Support", f), path.join(root, "CaseStudies/Support", f))
      }
      const reference = fs.readFileSync(path.join(refs, rel), "utf8")
      const result = await run(reference)
      expect(result.method).toBe("benchmark")
      expect(result.reasons).toEqual([])
      expect(result.status).toBe("accepted")
    },
    30 * 60_000,
  )

  test(
    "final gate rejects sorry, an extra axiom and native_decide",
    async () => {
      const reference = fs.readFileSync(path.join(refs, rel), "utf8")
      const alias = reference.indexOf("theorem CaseStudies.")
      expect((await run(fs.readFileSync(file, "utf8"))).reasons[0].code).toBe("FORBIDDEN_TOKEN")
      const axiom = reference.slice(0, alias) + "axiom gate_extra : False\n\n" + reference.slice(alias)
      expect((await run(axiom)).reasons[0].code).toBe("FORBIDDEN_TOKEN")
      const nd =
        reference.slice(0, alias) +
        "theorem gate_nd_helper : (2 : Nat) + 2 = 4 := by native_decide\n\n" +
        reference.slice(alias).replace(":=\n", ":= by\n  have _h := gate_nd_helper\n  exact\n")
      const result = await run(nd)
      expect(result.reasons[0].code).toBe("AXIOMS")
      // Lean 4.33: native_decide adds an auxiliary axiom `<decl>._native.native_decide.ax_…`
      expect(result.reasons[0].message).toContain("native_decide")
    },
    30 * 60_000,
  )

  test(
    "submission stage elaborates the file and flags errors inside the target",
    async () => {
      const baseline = fs.readFileSync(file, "utf8")
      const ok = await run(baseline.replace("  sorry\n", "  unfold ResponseTimeAnalysisEDF.Lemma3_05_statement\n  sorry\n"), "submission", true)
      expect(ok.reasons).toEqual([])
      const bad = await run(baseline.replace("  sorry\n", "  exact Nat.does_not_exist\n"), "submission", true)
      expect(bad.reasons[0].code).toBe("REGION_DOES_NOT_ELABORATE")
    },
    30 * 60_000,
  )
})
