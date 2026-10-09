import { describe, expect, test } from "bun:test"
import path from "path"
import { LeanStatementCheck } from "../../src/tool/lean-statement-check"
import { leanPropositionProblem } from "../../src/tool/proof-plan"
import { tmpdir } from "../fixture/fixture"

/** A minimal Lake project (core Lean only). */
async function project(dir: string) {
  await Bun.write(path.join(dir, "lakefile.lean"), "import Lake\nopen Lake DSL\npackage statement_check_test\n")
  await Bun.write(path.join(dir, "lean-toolchain"), "leanprover/lean4:v4.33.1\n")
}

describe("tool.lean-statement-check: prose normal forms (K7)", () => {
  test("rejects prose and truncated text, accepts Lean propositions", () => {
    expect(leanPropositionProblem("equality of nat sums")).toContain("prose")
    expect(leanPropositionProblem("the sum is bounded by the workload")).toContain("prose")
    expect(leanPropositionProblem("P j a b")).toBeUndefined()
    expect(leanPropositionProblem("(a + b ≤ c")).toBeTruthy()
    expect(leanPropositionProblem("")).toBeTruthy()
    expect(leanPropositionProblem("job_arrival j ≤ t")).toBeUndefined()
    expect(leanPropositionProblem("A")).toBeUndefined()
    expect(leanPropositionProblem("Function.Injective f")).toBeUndefined()
  })

  test("text equality needs no compiler", () => {
    expect(LeanStatementCheck.sameText("A  ∧ B /- c -/", "A ∧ B")).toBe(true)
    expect(LeanStatementCheck.cachedRegion("/x.lean", "g", "A ∧ B", "A ∧ ( B )")?.verdict).toBeUndefined()
  })
})

describe.skipIf(!Bun.which("lake"))("tool.lean-statement-check: elaboration (K6, K7)", () => {
  test("decides a root goal by definitional equality in the theorem's context", async () => {
    await using tmp = await tmpdir()
    await project(tmp.path)
    const file = path.join(tmp.path, "RootGoal.lean")
    const source = [
      "def Twice (n : Nat) : Prop := n + n = 2 * n",
      "namespace Demo",
      "theorem demo (n : Nat) (A B : Prop) : Twice n ∧ (A → B) := by",
      "  sorry",
      "end Demo",
      "",
    ].join("\n")
    await Bun.write(file, source)
    const check = (submitted: string) => LeanStatementCheck.rootGoal({ file, source, theorem: "demo", submitted })
    expect((await check("Twice n ∧ (A → B)")).verdict).toBe("equivalent")
    // formatting and notation differences elaborate to the same proposition
    expect((await check("And (n + n = 2 * n) (A → B)")).verdict).toBe("equivalent")
    const swapped = await check("(A → B) ∧ Twice n")
    expect(swapped.verdict).toBe("different")
    expect((await check("Twice n ∧ (A →")).verdict).toBe("different")
  }, 180000)

  test("compares region targets with plan normal forms inside the region's local context", async () => {
    await using tmp = await tmpdir()
    await project(tmp.path)
    const file = path.join(tmp.path, "Regions.lean")
    const source = [
      "def Pos (n : Nat) : Prop := 0 < n",
      "theorem demo (A B : Prop) (hA : A) (hB : B) : A ∧ B ∧ ∀ n : Nat, Pos (n + 1) := by",
      "  refine ⟨?_, ?_, ?_⟩",
      "  · exact hA",
      "  · exact hB",
      "  intro m",
      "  /- proof_region begin owner: lemma admit_id: gap-pos theorem: demo target: hm plan_node: n1 -/",
      "  have hm : Pos (m + 1) := (by",
      "    sorry)",
      "  /- proof_region end admit_id: gap-pos -/",
      "  /- proof_region begin owner: lemma admit_id: gap-and theorem: demo target: hab plan_node: n2 -/",
      "  have hab : A ∧ B := (by exact ⟨hA, hB⟩)",
      "  /- proof_region end admit_id: gap-and -/",
      "  exact hm",
      "",
    ].join("\n")
    await Bun.write(file, source)
    const verdicts = await LeanStatementCheck.regionTargets({
      file,
      source,
      pairs: [
        // uses the local `m` introduced before the region, and unfolds `Pos`
        { admit_id: "gap-pos", normal_form: "0 < m + 1" },
        { admit_id: "gap-and", normal_form: "B ∧ A" },
      ],
    })
    expect(verdicts.get("gap-pos")?.verdict).toBe("equivalent")
    expect(verdicts.get("gap-and")?.verdict).toBe("different")
    expect(LeanStatementCheck.cachedRegion(file, "gap-pos", "Pos (m + 1)", "0 < m + 1")?.verdict).toBe("equivalent")
  }, 180000)
})
