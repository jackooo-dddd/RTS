import { describe, expect, test } from "bun:test"
import { formatLeanSkillHints, leanSkillHintsFor } from "../../src/tool/lean-skill-hints"

function names(message: string) {
  return leanSkillHintsFor(message).map((hint) => hint.name)
}

describe("lean skill hints", () => {
  test("maps unsolved goals to goal focus guidance", () => {
    expect(names("unsolved goals\ncase h\nA B : Prop\n⊢ B")).toContain("goal-focus-discipline")
  })

  test("maps rewrite failures to rewrite discipline", () => {
    expect(names("tactic 'rewrite' failed, did not find instance of the pattern in the target expression")).toContain(
      "lean-rewrite-discipline",
    )
    expect(names("motive is not type correct")).toContain("lean-rewrite-discipline")
  })

  test("maps count and sum shapes to count bridging", () => {
    expect(names("type mismatch: List.countP p xs vs (List.filter p xs).length")).toContain("lean-count-bridging")
  })

  test("maps synthesis failures to goal-driven apply", () => {
    expect(names("typeclass instance problem is stuck, it is often due to metavariables")).toContain(
      "lean-goal-driven-apply",
    )
  })

  test("falls back to the general methodology and formats optional calls", () => {
    expect(names("something unexpected")).toEqual(["lean-proof-methodology"])
    const formatted = formatLeanSkillHints("application type mismatch")
    expect(formatted).toContain("<lean_skill_hints>")
    expect(formatted).toContain('skill({ name: "lean-proof-methodology" })')
  })
})
