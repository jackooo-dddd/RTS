import { afterAll, describe, expect, test } from "bun:test"
import fs from "fs"
import path from "path"
import { Instance } from "../../src/project/instance"
import { Session } from "../../src/session"
import { LeanSessionTool, LeanEquivalence, prepareSource, renderGoals } from "../../src/tool/lean-session"
import { Pantograph } from "../../src/tool/pantograph"
import type { Tool } from "../../src/tool/tool"
import { tmpdir } from "../fixture/fixture"

function context(sessionID: string, agent: Tool.Context["agent"] = "prover"): Tool.Context {
  return {
    sessionID,
    messageID: `msg_${sessionID}`,
    callID: `call_${sessionID}`,
    agent,
    abort: AbortSignal.any([]),
    messages: [],
    metadata: () => {},
    ask: async () => {},
  }
}

const HEADER = "import CaseStudies.ECRTS2005.Lemma3.Statement\n\n"
const OPENS = [
  "namespace CaseStudies.ECRTS2005.Lemma3",
  "open CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF",
  "universe u v",
  "",
].join("\n")
const INTROS =
  "intro sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq"

function testFile(regionA = "sorry", regionB = "sorry") {
  return (
    HEADER +
    OPENS +
    [
      "theorem lb_session_test : Lemma3_05_statement.{u, v} := by",
      "  unfold Lemma3_05_statement",
      `  ${INTROS}`,
      "  /- proof_region begin owner: lemma admit_id: A theorem: lb_session_test target: hA plan_node: n1 -/",
      "  have hA : ∀ j : Job, job_cost j = job_cost j := (by",
      `    ${regionA}`,
      "  )",
      "  /- proof_region end admit_id: A -/",
      "  /- proof_region begin owner: lemma admit_id: B theorem: lb_session_test target: hB plan_node: n2 -/",
      "  have hB : ∀ j : Job, job_arrival j + 0 = job_arrival j := (by",
      `    ${regionB}`,
      "  )",
      "  /- proof_region end admit_id: B -/",
      "  sorry",
      "",
      "end CaseStudies.ECRTS2005.Lemma3",
      "",
    ].join("\n")
  )
}

describe("lean_session source preparation", () => {
  test("strips the header, masks every region and cuts after the target", () => {
    const dir = fs.mkdtempSync("/tmp/lb-session-")
    fs.writeFileSync(path.join(dir, "lakefile.lean"), "")
    const file = path.join(dir, "Test.lean")
    const prepared = prepareSource(file, testFile("exact fun j => rfl", "simp"), "lb_session_test", "B")
    expect(prepared.modules).toEqual(["CaseStudies.ECRTS2005.Lemma3.Statement"])
    expect(prepared.body).not.toContain("import ")
    expect(prepared.body).toContain("have hA : ∀ j : Job, job_cost j = job_cost j := (by sorry)")
    expect(prepared.body).toContain("have hB : ∀ j : Job, job_arrival j + 0 = job_arrival j := (by sorry)")
    expect(prepared.body).not.toContain("end CaseStudies")
    expect(prepared.region?.target?.statement).toBe("∀ j : Job, job_arrival j + 0 = job_arrival j")
    expect(() => prepareSource(file, testFile(), "lb_session_test", "C")).toThrow("proof_region C not found")
    expect(() => prepareSource(file, testFile(), "nope")).toThrow("not found")
  })

  test("renders goals in Lean's display", () => {
    const goal: Pantograph.Goal = {
      name: "_uniq.1",
      target: { pp: "n + 0 = n" },
      vars: [{ name: "_uniq.0", userName: "n", type: { pp: "Nat" } }],
    }
    expect(renderGoals([goal])).toBe("n : Nat\n⊢ n + 0 = n")
    expect(renderGoals([])).toBe("No goals")
    expect(renderGoals([goal, goal])).toContain("case 2/2")
  })

  test("a missing Pantograph binary is a backend tool error, not a proof result", async () => {
    await using tmp = await tmpdir({ git: true })
    const previous = process.env.OPENCODE_PANTOGRAPH_REPL
    process.env.OPENCODE_PANTOGRAPH_REPL = path.join(tmp.path, "no-such-repl")
    try {
      await Instance.provide({
        directory: tmp.path,
        fn: async () => {
          await Bun.write(path.join(tmp.path, "lakefile.lean"), "")
          const file = path.join(tmp.path, "Test.lean")
          await Bun.write(file, testFile())
          const session = await Session.create({})
          const tool = await LeanSessionTool.init()
          const result = await tool.execute({ op: "open", file, theorem: "lb_session_test", scope: "theorem" }, context(session.id))
          expect(result.metadata).toMatchObject({ kind: "backend_error", code: "PANTOGRAPH_UNAVAILABLE" })
          expect(result.output).toContain("not a proof result")
          await Session.remove(session.id)
        },
      })
    } finally {
      if (previous === undefined) delete process.env.OPENCODE_PANTOGRAPH_REPL
      else process.env.OPENCODE_PANTOGRAPH_REPL = previous
      Pantograph.shutdownAll()
    }
  })
})

/**
 * Integration (built package, staged per D14; Pantograph 92d4818):
 *   PROSABUDDY_LEAN_INTEGRATION=1 LEANBUDDY_TEST_PACKAGE=<run copy> OPENCODE_PANTOGRAPH_REPL=<…/bin/repl>
 */
const integration =
  process.env.PROSABUDDY_LEAN_INTEGRATION === "1" && process.env.LEANBUDDY_TEST_PACKAGE && process.env.OPENCODE_PANTOGRAPH_REPL
describe.skipIf(!integration)("lean_session on Pantograph (integration)", () => {
  const root = process.env.LEANBUDDY_TEST_PACKAGE ?? ""
  const file = path.join(root, "CaseStudies/ECRTS2005/Lemma3/LbSessionTest.lean")
  afterAll(() => {
    fs.rmSync(file, { force: true })
    Pantograph.shutdownAll()
  })

  const withSession = async (fn: (tool: Awaited<ReturnType<typeof LeanSessionTool.init>>, ctx: Tool.Context) => Promise<void>) => {
    await Instance.provide({
      directory: root,
      fn: async () => {
        const session = await Session.create({})
        const tool = await LeanSessionTool.init()
        try {
          await fn(tool, context(session.id))
        } finally {
          await tool.execute({ op: "close" }, context(session.id)).catch(() => {})
          await Session.remove(session.id)
        }
      },
    })
  }

  test(
    "theorem scope: opens the real goal, runs tactics, classifies failures",
    async () => {
      fs.writeFileSync(file, testFile())
      await withSession(async (tool, ctx) => {
        const opened = await tool.execute({ op: "open", file, theorem: "lb_session_test", scope: "theorem" }, ctx)
        expect(opened.metadata.kind).toBe("proof_progress")
        // distil already presents the statement with its leading implicit binders introduced
        expect(opened.output).toContain("task_cost")
        const intro = await tool.execute({ op: "step", tactic: "intro task_cost task_period" }, ctx)
        expect(intro.metadata.kind).toBe("proof_progress")
        expect(intro.output).toContain("task_period : sporadic_task")
        expect(intro.output).not.toContain("✝✝")
        const bad = await tool.execute({ op: "step", tactic: "exact Nat.does_not_exist" }, ctx)
        expect(bad.metadata.kind).toBe("environment_problem")
        await expect(tool.execute({ op: "step", tactic: "sorry" }, ctx)).rejects.toThrow("forbidden")
        await expect(tool.execute({ op: "step", tactic: "native_decide" }, ctx)).rejects.toThrow("native_decide")
      })
    },
    600_000,
  )

  test(
    "region scope: the region's own goal, steps, snapshot and undo",
    async () => {
      fs.writeFileSync(file, testFile("exact Nat.broken_on_purpose", "sorry"))
      await withSession(async (tool, ctx) => {
        // region A is broken: masking keeps B openable (BACKEND_DECISION spike 3)
        const opened = await tool.execute({ op: "open", file, theorem: "lb_session_test", admit_id: "B" }, ctx)
        expect(opened.metadata).toMatchObject({ kind: "proof_progress", scope: "assigned_region", admit_id: "B" })
        expect(opened.output).toContain("⊢ ∀ (j : Job), job_arrival j + 0 = job_arrival j")
        expect(opened.output).toContain("hA : ∀ (j : Job), job_cost j = job_cost j\n")
        expect(opened.output).not.toContain("?m.")
        const intro = await tool.execute({ op: "step", tactic: "intro j" }, ctx)
        expect(intro.metadata.kind).toBe("proof_progress")
        expect(intro.output).toContain("⊢ job_arrival j + 0 = job_arrival j")
        const snap = await tool.execute({ op: "snapshot" }, ctx)
        const id = /Snapshot (snap_[0-9a-f]+)/.exec(snap.output)![1]
        const done = await tool.execute({ op: "step", tactic: "simp" }, ctx)
        expect(done.metadata.remaining_goals).toBe(0)
        expect(done.output).toContain("No goals")
        const back = await tool.execute({ op: "undo", snapshot_id: id }, ctx)
        expect(back.output).toContain("⊢ job_arrival j + 0 = job_arrival j")
        const audit = await tool.execute({ op: "inspect", left_expression: "job_arrival j + 0", right_expression: "job_arrival j" }, ctx)
        expect(audit.metadata.context_audit.outcome).toBe("convertible")
        const different = await tool.execute({ op: "inspect", left_expression: "(1 : Nat)", right_expression: "2" }, ctx)
        expect(different.metadata.context_audit.outcome).toBe("not_convertible")
        await expect(tool.execute({ op: "inspect", left_expression: "_", right_expression: "1" }, ctx)).rejects.toThrow("hole")
      })
    },
    600_000,
  )

  test(
    "expected goal is compared by definitional equality, not text",
    async () => {
      fs.writeFileSync(file, testFile())
      await withSession(async (tool, ctx) => {
        const same = await tool.execute(
          { op: "open", file, theorem: "lb_session_test", admit_id: "B", expected_goal: "∀ (j : Job), job_arrival j = job_arrival j" },
          ctx,
        )
        expect(same.metadata.kind).toBe("proof_progress")
        const other = await tool.execute(
          { op: "open", file, theorem: "lb_session_test", admit_id: "B", expected_goal: "∀ (j : Job), job_cost j = 0" },
          ctx,
        )
        expect(other.metadata.kind).toBe("session_state_desync")
        const blocked = await tool.execute({ op: "step", tactic: "intro j" }, ctx)
        expect(blocked.metadata).toMatchObject({ kind: "session_state_desync", tactic_applied: false })
      })
    },
    600_000,
  )

  test(
    "a source change re-opens from the file and replays the successful tactics",
    async () => {
      fs.writeFileSync(file, testFile())
      await withSession(async (tool, ctx) => {
        await tool.execute({ op: "open", file, theorem: "lb_session_test", admit_id: "B" }, ctx)
        await tool.execute({ op: "step", tactic: "intro j" }, ctx)
        fs.writeFileSync(file, testFile("intro j\n    rfl", "sorry"))
        const goal = await tool.execute({ op: "goal" }, ctx)
        expect(goal.metadata.resynced).toBe(true)
        expect(goal.output).toContain("⊢ job_arrival j + 0 = job_arrival j")
      })
    },
    600_000,
  )

  test(
    "statement equivalence service: alpha-equivalent and defeq accepted, different rejected, holes refused",
    async () => {
      const modules = ["CaseStudies.ECRTS2005.Lemma3.Statement"]
      const target = path.join(root, "CaseStudies/ECRTS2005/Lemma3/Solution.lean")
      expect((await LeanEquivalence.equivalentClosed({ file: target, modules, a: "∀ n : Nat, n + 0 = n", b: "∀ (k : Nat), k + 0 = k" })).verdict).toBe(
        "equivalent",
      )
      expect((await LeanEquivalence.equivalentClosed({ file: target, modules, a: "∀ n : Nat, n + 0 = n", b: "∀ n : Nat, n = n" })).verdict).toBe(
        "equivalent",
      )
      expect((await LeanEquivalence.equivalentClosed({ file: target, modules, a: "∀ n : Nat, n + 0 = n", b: "∀ n : Nat, n + 1 = n" })).verdict).toBe(
        "different",
      )
      expect((await LeanEquivalence.equivalentClosed({ file: target, modules, a: "∀ n : Nat, n + 0 = n", b: "_" })).verdict).toBe(
        "b_does_not_elaborate",
      )
      const statement = "CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF.Lemma3_05_statement"
      const folded = await LeanEquivalence.equivalentClosed({
        file: target,
        modules,
        a: `${statement}.{u, v}`,
        b: `${statement}.{u, v}`,
        levels: ["u", "v"],
      })
      expect(folded.verdict).toBe("equivalent")
    },
    600_000,
  )
})
