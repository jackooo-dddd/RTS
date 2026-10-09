import { describe, expect, test } from "bun:test"
import path from "path"
import { auditCandidateLemma } from "../../src/tool/proof-premise-audit"
import { ProofPlanCandidateLemma } from "../../src/tool/proof-schema"
import { Instance } from "../../src/project/instance"
import { tmpdir } from "../fixture/fixture"

function candidate(name: string, role: "direct_apply" | "rewrite" | "transport" | "local_fact" | "automation_hint" = "direct_apply") {
  return ProofPlanCandidateLemma.parse({
    name,
    library: "local",
    role,
    reason: "premise-audit fixture",
  })
}

/** A minimal Lake project (core Lean only): the audit elaborates its probe with `lake env lean`. */
async function project(dir: string) {
  await Bun.write(path.join(dir, "lakefile.lean"), "import Lake\nopen Lake DSL\npackage audit_test\n")
  await Bun.write(path.join(dir, "lean-toolchain"), "leanprover/lean4:v4.33.1\n")
}

async function audit(source: string, fileName: string, theorem: string, formalGoal: string, name: string, role?: Parameters<typeof candidate>[1]) {
  await using tmp = await tmpdir({ git: true })
  await project(tmp.path)
  const file = path.join(tmp.path, fileName)
  await Bun.write(file, source)
  // await here: `await using` removes the directory when this function returns
  return await Instance.provide({
    directory: tmp.path,
    fn: () => auditCandidateLemma({ file, source, theorem, formalGoal, candidate: candidate(name, role) }),
  })
}

describe.skipIf(!Bun.which("lake"))("tool.proof-premise-audit", () => {
  test("accepts a candidate whose premises are locally available", async () => {
    const result = await audit(
      [
        "axiom pair_intro : ∀ P Q : Prop, P → Q → P ∧ Q",
        "theorem demo (P Q : Prop) (HP : P) (HQ : Q) : P ∧ Q := by",
        "  sorry",
        "",
      ].join("\n"),
      "AuditUsable.lean",
      "demo",
      "P ∧ Q",
      "pair_intro",
    )
    expect(result.verdict).toBe("usable")
    expect(result.residual_premises).toEqual([])
    expect(result.instantiation_fingerprint).toBeTruthy()
  }, 120000)

  test("reports a residual premise instead of approving an inapplicable route", async () => {
    const result = await audit(
      [
        "axiom pair_intro : ∀ P Q : Prop, P → Q → P ∧ Q",
        "theorem demo (P Q : Prop) (HP : P) : P ∧ Q := by",
        "  sorry",
        "",
      ].join("\n"),
      "AuditMissing.lean",
      "demo",
      "P ∧ Q",
      "pair_intro",
    )
    expect(result.verdict).toBe("bridge_required")
    expect(result.residual_premises).toEqual(["Q"])
    expect(result.residual_premise_fingerprints).toHaveLength(result.residual_premises.length)
  }, 120000)

  test("introduces node-local binders before probing the candidate conclusion", async () => {
    const result = await audit(
      [
        "axiom pointwise {T : Type} {P Q : T → Prop} (x : T) : P x → Q x",
        "theorem demo (T : Type) (P Q : T → Prop) : True := by",
        "  exact trivial",
        "",
      ].join("\n"),
      "AuditQuantified.lean",
      "demo",
      "∀ x : T, P x → Q x",
      "pointwise",
    )
    // `apply` must meet the node conclusion `Q x` after the node's own binders are introduced
    expect(result.verdict).toBe("usable")
    expect(result.residual_premises).toEqual([])
  }, 120000)

  test("audits private theorem declarations as targets", async () => {
    const result = await audit(
      [
        "axiom identity_fact : ∀ P : Prop, P → P",
        "private theorem demo (P : Prop) (HP : P) : P := by",
        "  sorry",
        "",
      ].join("\n"),
      "AuditPrivate.lean",
      "demo",
      "P",
      "identity_fact",
    )
    expect(result.verdict).toBe("usable")
  }, 120000)

  test("checks rewrite candidates for availability without requiring whole-node closure", async () => {
    const result = await audit(
      [
        "axiom rewrite_piece : ∀ P Q : Prop, P = Q",
        "theorem demo (A B : Prop) : A ∧ B := by",
        "  sorry",
        "",
      ].join("\n"),
      "AuditRewrite.lean",
      "demo",
      "A ∧ B",
      "rewrite_piece",
      "rewrite",
    )
    expect(result.verdict).toBe("available")
    expect(result.exact_type).toContain("rewrite_piece")
    expect(result.residual_premises).toEqual([])
  }, 120000)

  test("an unknown candidate is an interface mismatch", async () => {
    const result = await audit(
      ["theorem demo (P : Prop) (HP : P) : P := by", "  sorry", ""].join("\n"),
      "AuditUnknown.lean",
      "demo",
      "P",
      "no_such_lemma",
    )
    expect(result.verdict).toBe("interface_mismatch")
    expect(result.diagnostic).toContain("no_such_lemma")
  }, 120000)
})
