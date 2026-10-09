import { afterAll, describe, expect, test } from "bun:test"
import fs from "fs"
import path from "path"
import { Instance } from "../../src/project/instance"
import { Session } from "../../src/session"
import { LeanCheckTool } from "../../src/tool/lean-check"
import { LeanQueryTool } from "../../src/tool/lean-query"
import { Pantograph } from "../../src/tool/pantograph"
import type { Tool } from "../../src/tool/tool"

/**
 * lean_query and lean_check against the built package (staged per D14):
 *   PROSABUDDY_LEAN_INTEGRATION=1 LEANBUDDY_TEST_PACKAGE=<run copy> OPENCODE_PANTOGRAPH_REPL=<…/bin/repl>
 */
const integration =
  process.env.PROSABUDDY_LEAN_INTEGRATION === "1" && process.env.LEANBUDDY_TEST_PACKAGE && process.env.OPENCODE_PANTOGRAPH_REPL

function context(sessionID: string): Tool.Context {
  return {
    sessionID,
    messageID: `msg_${sessionID}`,
    callID: `call_${sessionID}`,
    agent: "prover",
    abort: AbortSignal.any([]),
    messages: [],
    metadata: () => {},
    ask: async () => {},
  }
}

describe.skipIf(!integration)("lean_query and lean_check (integration)", () => {
  const root = process.env.LEANBUDDY_TEST_PACKAGE ?? ""
  const solution = path.join(root, "CaseStudies/ECRTS2005/Lemma3/Solution.lean")
  const scratch = path.join(root, "CaseStudies/ECRTS2005/Lemma3/LbToolsTest.lean")
  afterAll(() => {
    fs.rmSync(scratch, { force: true })
    Pantograph.shutdownAll()
  })

  const run = async (fn: (ctx: Tool.Context) => Promise<void>) => {
    await Instance.provide({
      directory: root,
      fn: async () => {
        const session = await Session.create({})
        try {
          await fn(context(session.id))
        } finally {
          await Session.remove(session.id)
        }
      },
    })
  }

  test(
    "lean_query check/print/search in the file's context (opens and namespaces apply)",
    async () => {
      await run(async (ctx) => {
        const query = await LeanQueryTool.init()
        // `Lemma3_05_statement` resolves only through the file's `open … ResponseTimeAnalysisEDF`
        const check = await query.execute({ command: "check", input: "Lemma3_05_statement", file: solution, theorem: "solution" }, ctx)
        expect(check.metadata.error).toBe(false)
        expect(check.output).toContain("Prop")
        const print = await query.execute({ command: "print", input: "Prosa.Util.Sum.sumFiltered", file: solution }, ctx)
        expect(print.metadata.error).toBe(false)
        expect(print.output).toContain("sumFiltered")
        const search = await query.execute({ command: "search", input: "sumFiltered", file: solution }, ctx)
        expect(search.metadata.matches).toBeGreaterThan(0)
        expect(search.output).toContain("Prosa.Util.Sum.sumFiltered")
        const unknown = await query.execute({ command: "check", input: "Nat.no_such_lemma", file: solution }, ctx)
        expect(unknown.metadata.error).toBe(true)
        await expect(query.execute({ command: "check", input: "by simp", file: solution }, ctx)).rejects.toThrow("tactic block")
      })
    },
    600_000,
  )

  test(
    "lean_check reports unfinished proofs as non-final and errors with their line",
    async () => {
      await run(async (ctx) => {
        const check = await LeanCheckTool.init()
        const ok = await check.execute({ filePath: solution }, ctx)
        expect(ok.metadata.status).toBe("success")
        expect(ok.output).toContain("unfinished: 1 declaration(s) use `sorry`")
        const source = fs.readFileSync(solution, "utf8")
        const sorryLine = source.split("\n").findIndex((line) => line === "  sorry") + 1
        fs.writeFileSync(scratch, source.replace("  sorry\n", "  exact Nat.does_not_exist\n"))
        const bad = await check.execute({ filePath: scratch }, ctx)
        expect(bad.metadata.status).toBe("fail")
        expect(bad.metadata.errors[0].line).toBe(sorryLine)
        expect(bad.output).toContain("does_not_exist")
      })
    },
    600_000,
  )
})
