import { describe, expect, test } from "bun:test"
import { LeanRegion } from "../../src/tool/lean-region"

const FILE = `theorem t (n : Nat) (f : Nat → Nat := fun x => (x)) : n + 0 = n ∧ 0 + n = n := by
  /- proof_region begin owner: lemma admit_id: A theorem: t target: hA plan_node: n1 -/
  have hA : n + 0 = n := (by
    -- a comment with a stray ) paren
    have helper : (n) = n := (by rfl)
    simp [show "str)" = "str)" from rfl]
  )
  /- proof_region end admit_id: A -/
  -- proof_region begin owner: lemma admit_id: B theorem: t target: hB plan_node: n2
  have hB : 0 + n = n := (by
    sorry
  )
  -- proof_region end admit_id: B
  exact ⟨hA, hB⟩
`

describe("LeanRegion", () => {
  test("parses block and line markers with their attributes", () => {
    const { regions, errors } = LeanRegion.parse(FILE)
    expect(errors).toEqual([])
    expect(regions.map((r) => r.admit_id)).toEqual(["A", "B"])
    expect(regions[0].attributes).toMatchObject({ owner: "lemma", theorem: "t", target: "hA", plan_node: "n1" })
    expect(regions[1].attributes.plan_node).toBe("n2")
  })

  test("matches the outer wrapper across comments, strings and nested wrappers", () => {
    const { regions } = LeanRegion.parse(FILE)
    const a = regions[0].target!
    expect(a.name).toBe("hA")
    expect(a.statement).toBe("n + 0 = n")
    expect(FILE[a.open]).toBe("(")
    expect(FILE[a.close]).toBe(")")
    expect(FILE.slice(a.close - 3, a.close + 1)).toBe("\n  )")
    expect(regions[1].target!.statement).toBe("0 + n = n")
  })

  test("values run to the next known field and keep Lean terms with colons", () => {
    const attrs = LeanRegion.attributes("admit_id: X target: h plan_node: n (x : Job) theorem: solution")
    expect(attrs).toEqual({ admit_id: "X", target: "h", plan_node: "n (x : Job)", theorem: "solution" })
  })

  test("masks region proofs to `(by sorry)` without touching the rest", () => {
    const { regions } = LeanRegion.parse(FILE)
    const masked = LeanRegion.maskRegions(FILE, regions)
    expect(masked).toContain("have hA : n + 0 = n := (by sorry)")
    expect(masked).toContain("have hB : 0 + n = n := (by sorry)")
    expect(masked).toContain("exact ⟨hA, hB⟩")
    expect(masked).not.toContain("helper")
    expect(LeanRegion.parse(masked).regions.map((r) => r.target?.name)).toEqual(["hA", "hB"])
  })

  test("reports structural errors instead of guessing", () => {
    const noEnd = "/- proof_region begin admit_id: X -/\nhave h : True := (by trivial)\n"
    expect(LeanRegion.parse(noEnd).errors[0].message).toContain("no end marker")
    const noWrapper = "/- proof_region begin admit_id: X -/\nhave h : True := by trivial\n/- proof_region end admit_id: X -/\n"
    expect(LeanRegion.parse(noWrapper).errors[0].message).toContain("no `have")
    const unbalanced = "/- proof_region begin admit_id: X -/\nhave h : True := (by trivial\n/- proof_region end admit_id: X -/\n"
    expect(LeanRegion.parse(unbalanced).errors[0].message).toContain("unbalanced")
    const noAdmit = "/- proof_region begin owner: lemma -/\n"
    expect(LeanRegion.parse(noAdmit).errors[0].message).toContain("without admit_id")
  })

  test("primes in identifiers are not char literals", () => {
    const src = "/- proof_region begin admit_id: P -/\nhave h' : a' = a' := (by\n  exact rfl\n)\n/- proof_region end admit_id: P -/\n"
    const region = LeanRegion.parse(src).regions[0]
    expect(region.target!.name).toBe("h'")
    expect(src[region.target!.close]).toBe(")")
  })
})
