import { describe, expect, test } from "bun:test"
import { LeanTerm } from "../../src/tool/lean-term"

const ok = (text: string) => {
  const r = LeanTerm.scan(text)
  return r.ok ? r.text : `REJECT ${r.token}`
}

describe("LeanTerm.scan (lean_session-equivalence.md token rules)", () => {
  test("accepts identifiers with underscores, primes, ? and !", () => {
    expect(ok("Lemma3_05_statement")).toBe("Lemma3_05_statement")
    expect(ok("∀ j, job_cost j ≤ task_cost (job_task j)")).toBe("∀ j, job_cost j ≤ task_cost (job_task j)")
    expect(ok("l.get? 0 = some x ∧ o.get! = y'")).toBe("l.get? 0 = some x ∧ o.get! = y'")
    expect(ok("CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF.Lemma3_05_statement.{u, v}")).toContain("Lemma3_05")
  })

  test("accepts `_` as a binder name", () => {
    expect(ok("fun _ => 0")).toBe("fun _ => 0")
    expect(ok("∀ _ : Nat, True")).toBe("∀ _ : Nat, True")
    expect(ok("∃ _, True")).toBe("∃ _, True")
    expect(ok("∀ (_ : Nat) (x : Nat), x = x")).toBe("∀ (_ : Nat) (x : Nat), x = x")
    expect(ok("fun x _ => x")).toBe("fun x _ => x")
  })

  test("maps universe metavariables to the level hole", () => {
    expect(ok("∀ {α : Sort ?u.12}, α → α")).toBe("∀ {α : Sort _}, α → α")
    expect(ok("∀ {α : Type ?u.7}, α → α")).toBe("∀ {α : Type _}, α → α")
    expect(ok("@id.{?u.3} Nat 0 = 0")).toBe("@id.{_} Nat 0 = 0")
  })

  test("rejects term holes, metavariables and sorry", () => {
    expect(ok("f _ x = y")).toBe("REJECT _")
    expect(ok("_")).toBe("REJECT _")
    expect(ok("?x = 1")).toBe("REJECT ?x")
    expect(ok("?_")).toBe("REJECT ?_")
    expect(ok("sorry")).toBe("REJECT sorry")
    expect(ok("a = sorryAx Nat")).toBe("REJECT sorryAx")
    // `?u.N` outside a universe position is a term metavariable
    expect(ok("?u.3 = 0")).toBe("REJECT ?u.3")
  })

  test("assertPureTerm rejects tactic blocks and commands", () => {
    expect(() => LeanTerm.assertPureTerm("x", "by simp")).toThrow("tactic block")
    expect(() => LeanTerm.assertPureTerm("x", "#eval 1")).toThrow("#")
    expect(() => LeanTerm.assertPureTerm("x", "(a = b")).toThrow("unbalanced")
    expect(() => LeanTerm.assertPureTerm("x", "a = b\ntheorem t : True := trivial")).toThrow("command")
    expect(() => LeanTerm.assertPureTerm("x", "∀ x : Nat, x + 0 = x")).not.toThrow()
  })
})
