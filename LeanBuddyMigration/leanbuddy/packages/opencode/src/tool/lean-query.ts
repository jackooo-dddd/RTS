import z from "zod"
import path from "path"
import os from "os"
import fs from "fs/promises"
import { Tool } from "./tool"
import DESCRIPTION from "./lean-query.txt"
import { Instance } from "../project/instance"
import { ProofEditTransaction } from "@/session/proof-edit-transaction"
import { SessionProof } from "@/session/session-proof"
import { LeanProject } from "./lean-project"
import { LeanSource } from "./lean-source"
import { LeanTerm } from "./lean-term"
import { Pantograph } from "./pantograph"

/**
 * `lean_query`: read-only declaration and type queries in the target file's real context (DECISIONS D2; tools-advices
 * coqtop-revision.md). `check` and `print` run `#check`/`#print` through Pantograph's `frontend.process` on the file
 * text up to the target theorem, so namespaces, `open`s, `variable`s and helper declarations are those of the file.
 * `search` finds declaration names in the loaded environment. Counts as a passive lookup for the stall guards.
 */

const catalogs = new Map<string, { generation: number; names: string[] }>()
const SEARCH_LIMIT = 40

function compact(text: string, limit = 6000) {
  return text.length <= limit ? text : text.slice(0, limit) + "\n…(truncated)"
}

async function contextText(sessionID: string, file: string, theorem?: string) {
  const content = await ProofEditTransaction.readSource(sessionID, file)
  const header = LeanSource.header(content)
  const body = content.slice(header.bodyOffset)
  const decl = theorem ? LeanSource.findDeclaration(body, theorem) : undefined
  return { modules: header.imports, prefix: decl ? body.slice(0, decl.start) : body, bodyLine: header.bodyLine }
}

type ProcessResult = { units: { boundary: [number, number]; messages: { severity: string; data: string; pos?: { line: number } }[] }[] }

export const LeanQueryTool = Tool.define("lean_query", {
  description: DESCRIPTION,
  parameters: z.object({
    command: z.enum(["check", "print", "search"]).describe("check: type of a term; print: a declaration; search: declaration names"),
    input: z.string().min(1).max(2000).describe("check: a term; print: a declaration name; search: a name fragment (case-insensitive, `*` wildcard)"),
    file: z.string().optional().describe("The .lean file whose context to use (default: the bound proof file)"),
    theorem: z.string().optional().describe("Query in the context just before this declaration (default: end of the file)"),
  }),
  async execute(params, ctx): Promise<{ title: string; output: string; metadata: Record<string, any> }> {
    await ctx.ask({ permission: "lean_query", patterns: ["*"], always: ["*"], metadata: { command: params.command } })
    const bound = SessionProof.get(ctx.sessionID)?.file
    const raw = params.file ?? bound
    if (!raw) throw new Error("lean_query needs a file: pass `file` (a .lean file of the project)")
    const file = path.isAbsolute(raw) ? raw : path.resolve(Instance.directory, raw)
    if (!file.endsWith(".lean")) throw new Error("lean_query works in the context of a .lean file")
    const root = LeanProject.findRoot(file)
    if (!root) throw new Error(`no Lake project contains ${file}`)
    const context = await contextText(ctx.sessionID, file, params.theorem)
    const proc = Pantograph.forProject(root, context.modules)

    try {
      if (params.command === "search") {
        const fragment = params.input.trim()
        if (!/^[\p{L}\p{N}_.'*?!]+$/u.test(fragment)) throw new Error("search takes a name fragment (letters, digits, `_`, `.`, `*`)")
        let catalog = catalogs.get(proc.key)
        if (!catalog || catalog.generation !== proc.generation) {
          // 0.3.19 writes the catalog to a file (one name per line) and returns only the count
          const out = path.join(os.tmpdir(), `leanbuddy-catalog-${process.pid}-${Date.now()}.txt`)
          await proc.request<{ nSymbols: number }>("env.catalog", { filename: out, invertFilter: false }, 300_000)
          const names = (await fs.readFile(out, "utf8")).split("\n").filter(Boolean)
          await fs.rm(out, { force: true })
          catalog = { generation: proc.generation, names }
          catalogs.set(proc.key, catalog)
        }
        const pattern = new RegExp(fragment.replace(/[.+?^${}()|[\]\\]/g, "\\$&").replace(/\*/g, ".*"), "i")
        const hits = catalog.names
          .filter((name) => pattern.test(name) && !/\._|_private\.|\.proof_\d+$|\.match_\d+$|\.eq_\d+$/.test(name))
          .sort((a, b) => a.length - b.length || a.localeCompare(b))
        const shown = hits.slice(0, SEARCH_LIMIT)
        const typed: string[] = []
        for (const name of shown.slice(0, 12)) {
          const info = await proc.request<{ type?: Pantograph.Expression }>("env.inspect", { name }).catch(() => undefined)
          typed.push(info?.type?.pp ? `${name} : ${info.type.pp.replace(/\s+/g, " ").slice(0, 400)}` : name)
        }
        const rest = shown.slice(12)
        return {
          title: `lean_query search ${fragment}: ${hits.length} match(es)`,
          output: [
            ...typed,
            ...rest,
            hits.length > SEARCH_LIMIT ? `… ${hits.length - SEARCH_LIMIT} more; refine the fragment` : undefined,
            hits.length === 0 ? "no declaration name matches" : undefined,
          ]
            .filter((line): line is string => Boolean(line))
            .join("\n"),
          metadata: { command: "search", matches: hits.length },
        }
      }

      let command: string
      if (params.command === "check") {
        LeanTerm.assertPureTerm("input", params.input)
        command = `#check (${params.input})`
      } else {
        if (!/^@?[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}\p{N}_'!?]+)*$/u.test(params.input.trim())) throw new Error("print takes one declaration name")
        command = `#print ${params.input.trim()}`
      }
      const text = `${context.prefix.replace(/\s*$/, "\n\n")}${command}\n`
      const queryLine = text.split("\n").length - 1
      const reply = await proc.request<ProcessResult>("frontend.process", { file: text, readHeader: false, inheritEnv: false, newConstants: false })
      const messages = reply.units.flatMap((unit) => unit.messages)
      const own = messages.filter((m) => (m.pos?.line ?? 0) >= queryLine)
      const errors = own.filter((m) => m.severity === "error")
      const output = own.map((m) => m.data.trim()).join("\n") || "(no output)"
      return {
        title: `lean_query ${params.command}${errors.length ? ": error" : ""}`,
        output: compact(output),
        metadata: { command: params.command, error: errors.length > 0 },
      }
    } catch (error) {
      if (error instanceof Pantograph.PantographError) {
        return {
          title: `lean_query ${params.command}: ${error.kind === "backend" ? "backend error" : "error"}`,
          output: `${error.kind === "backend" ? "backend_error" : "error"} [${error.code}]: ${error.message}`,
          metadata: { command: params.command, error: true, kind: error.kind === "backend" ? "backend_error" : "command_error" },
        }
      }
      throw error
    }
  },
})
