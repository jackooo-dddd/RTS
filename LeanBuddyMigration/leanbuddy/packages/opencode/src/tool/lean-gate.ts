import fs from "fs/promises"
import os from "os"
import path from "path"
import { createHash } from "crypto"
import { SessionProof } from "@/session/session-proof"
import { ProofEditTransaction } from "@/session/proof-edit-transaction"
import { Filesystem } from "../util/filesystem"
import { runProcess } from "./coq-project"
import { LeanProject } from "./lean-project"
import { LeanSource } from "./lean-source"

/**
 * The Lean proof-integrity gate (DECISIONS D4; replaces the Rocq AST audit). Two stages:
 *
 * - `final`: the theorem is complete. Benchmark mode (the file is a `solution_file` of `benchmark/tasks.json`) runs
 *   `benchmark/check.py` itself when the candidate is the file on disk, otherwise the same five checks on a
 *   temporary copy: frozen files unchanged, forbidden tokens, the module and its helper modules build/elaborate,
 *   `theorem gate_check : <statement> := <solution>`, and `#print axioms` within the allowed three.
 *   General mode applies the same checks to the target declaration, with its baseline type as the statement.
 * - `submission`: a lemma helper's result. Only the target's proof may change (plus `import`s of package modules,
 *   KNOWN_PROBLEMS K1), no forbidden token in it (`sorry` optionally allowed), and the file elaborates without
 *   errors in the target declaration.
 *
 * The public shape (`Stage`, `Result`, `runForSession`, `passed`, `formatReasons`, `maxSubmissionRepairs`) is that
 * of the former `LeanGate`, so callers change only by name.
 */
export namespace LeanGate {
  export type Stage = "submission" | "final"
  export type Mode = "off" | "auto" | "required"

  export type Reason = {
    code: string
    message: string
    file?: string
    line?: number
    details?: Record<string, unknown>
  }

  export type Result = {
    status: "accepted" | "rejected" | "error" | "disabled"
    stage: Stage
    mode: Mode
    theorem?: string
    /** `benchmark` (check.py or its TypeScript equivalent) or `general`. */
    method?: "check.py" | "benchmark" | "general"
    task?: string
    reasons: Reason[]
    diagnostics: string[]
    axioms?: string[]
    baseline_hash?: string
    candidate_hash?: string
    transaction_id?: string
  }

  export type Config = {
    mode: Mode
    timeoutMs: number
    importRoots: string[]
    python: string
  }

  function positiveInteger(raw: string | undefined, fallback: number) {
    if (!raw) return fallback
    const parsed = Number.parseInt(raw, 10)
    return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback
  }

  function mode(): Mode {
    const raw = process.env.OPENCODE_LEAN_GATE?.trim().toLowerCase()
    if (!raw) return "auto"
    if (raw === "off" || raw === "auto" || raw === "required") return raw
    // Invalid security configuration must not silently disable the gate.
    return "required"
  }

  export function config(): Config {
    return {
      mode: mode(),
      // `lake build` of a case study takes minutes when helper modules change; never the 2-minute Rocq default.
      timeoutMs: positiveInteger(process.env.OPENCODE_LEAN_GATE_TIMEOUT_MS, LeanProject.DEFAULT_TIMEOUT_MS),
      importRoots: (process.env.OPENCODE_LEAN_GATE_IMPORT_ROOTS ?? "Prosa,Mathlib,CaseStudies")
        .split(",")
        .map((item) => item.trim())
        .filter(Boolean),
      python: process.env.OPENCODE_LEAN_GATE_PYTHON?.trim() || "python3",
    }
  }

  export function maxSubmissionRepairs() {
    return positiveInteger(process.env.OPENCODE_LEAN_GATE_MAX_REPAIRS, 2)
  }

  function hash(source: string) {
    return createHash("sha256").update(source).digest("hex")
  }

  export function passed(result: Result) {
    return result.status === "accepted" || result.status === "disabled"
  }

  export function formatReasons(result: Result) {
    return result.reasons.map((reason) => {
      const location = reason.line ? ` line ${reason.line}` : ""
      return `- [${reason.code}]${location}: ${reason.message}`
    })
  }

  // ---------------------------------------------------------------------------------------------------------
  // Benchmark task lookup

  export type BenchmarkTask = {
    id: string
    statement_module: string
    statement_file: string
    statement: string
    universes: string[]
    solution_module: string
    solution_file: string
    solution: string
  }

  /** The case-study task whose `solution_file` is `file`, if `file` lies in a package with `benchmark/tasks.json`. */
  export async function benchmarkTask(file: string): Promise<{ root: string; task: BenchmarkTask } | undefined> {
    const root = LeanProject.findRoot(file)
    if (!root) return undefined
    const tasksFile = path.join(root, "benchmark", "tasks.json")
    if (!(await Filesystem.exists(tasksFile))) return undefined
    try {
      const tasks = JSON.parse(await Filesystem.readText(tasksFile)) as BenchmarkTask[]
      const rel = path.relative(root, path.resolve(file)).split(path.sep).join("/")
      const task = tasks.find((item) => item.solution_file === rel)
      return task ? { root, task } : undefined
    } catch {
      return undefined
    }
  }

  // ---------------------------------------------------------------------------------------------------------
  // check.py reason mapping

  /** Map a `benchmark/check.py` FAIL detail to a gate reason code. */
  export function checkPyReasonCode(detail: string) {
    if (detail.startsWith("read-only files were changed")) return "FROZEN_CHANGED"
    if (detail.startsWith("solution file missing")) return "SOLUTION_MISSING"
    if (detail.startsWith("forbidden token")) return "FORBIDDEN_TOKEN"
    if (detail.startsWith("build failed (timeout)")) return "BUILD_TIMEOUT"
    if (detail.startsWith("build failed")) return "BUILD_FAILED"
    if (detail.startsWith("the solution does not prove the frozen statement")) return "STATEMENT_MISMATCH"
    if (detail.startsWith("could not read the axioms")) return "AXIOMS_UNREADABLE"
    if (detail.startsWith("uses non-standard axioms")) return "AXIOMS"
    return "CHECK_FAILED"
  }

  /** Axioms listed by `#print axioms` output, or undefined when the output has no axiom report. */
  export function parseAxioms(output: string) {
    if (output.includes("does not depend on any axioms")) return [] as string[]
    const match = /depends on axioms: \[([\s\S]*?)\]/.exec(output)
    if (!match) return undefined
    return match[1]
      .split(",")
      .map((item) => item.trim())
      .filter(Boolean)
  }

  // ---------------------------------------------------------------------------------------------------------
  // Frozen files and helper modules (same rules as check.py)

  type Frozen = { files: Record<string, string>; closed_trees: string[] }

  async function frozenViolations(root: string) {
    const frozenFile = path.join(root, "benchmark", "frozen_sha256.json")
    const frozen = JSON.parse(await Filesystem.readText(frozenFile)) as Frozen
    const bad: string[] = []
    for (const [rel, expected] of Object.entries(frozen.files)) {
      const p = path.join(root, rel)
      const data = await fs.readFile(p).catch(() => undefined)
      if (!data) bad.push(`missing: ${rel}`)
      else if (createHash("sha256").update(data).digest("hex") !== expected) bad.push(`modified: ${rel}`)
    }
    for (const tree of frozen.closed_trees ?? []) {
      for await (const rel of walk(path.join(root, tree), root)) {
        if (!(rel in frozen.files) && path.basename(rel) !== ".DS_Store") bad.push(`added: ${rel}`)
      }
    }
    return { bad, frozen }
  }

  async function* walk(dir: string, root: string): AsyncGenerator<string> {
    const entries = await fs.readdir(dir, { withFileTypes: true }).catch(() => [])
    for (const entry of entries) {
      const full = path.join(dir, entry.name)
      if (entry.isDirectory()) yield* walk(full, root)
      else if (entry.isFile()) yield path.relative(root, full).split(path.sep).join("/")
    }
  }

  /** Non-frozen `CaseStudies.*` modules imported (transitively) by `source`: the files a solver wrote. */
  async function helperModules(root: string, source: string, frozen: Frozen) {
    const seen: string[] = []
    const todo = [...importsOf(source).filter((m) => m.startsWith("CaseStudies."))]
    while (todo.length) {
      const module = todo.pop()!
      if (seen.includes(module)) continue
      const rel = module.split(".").join("/") + ".lean"
      if (rel in frozen.files) continue
      seen.push(module)
      const text = await Filesystem.readText(path.join(root, rel)).catch(() => undefined)
      if (text !== undefined) todo.push(...importsOf(text).filter((m) => m.startsWith("CaseStudies.")))
    }
    return seen
  }

  function importsOf(source: string) {
    return [...LeanSource.stripComments(source).matchAll(/^import\s+(CaseStudies\.\S+)/gm)].map((m) => m[1])
  }

  // ---------------------------------------------------------------------------------------------------------
  // Final stage

  type FinalInput = {
    file: string
    theorem: string
    baselineSource: string
    candidateSource: string
    signal?: AbortSignal
  }

  async function finalWithCheckPy(root: string, task: BenchmarkTask, settings: Config, signal?: AbortSignal) {
    const out = path.join(await fs.mkdtemp(path.join(os.tmpdir(), "leanbuddy-gate-")), "result.json")
    try {
      const timeoutSeconds = Math.max(60, Math.floor(settings.timeoutMs / 1000))
      const result = await runProcess(
        [settings.python, "benchmark/check.py", task.id, "--json", out, "--timeout", String(timeoutSeconds)],
        root,
        { timeoutMs: settings.timeoutMs * 3, signal },
      )
      const parsed = JSON.parse(await Filesystem.readText(out).catch(() => "[]")) as {
        id: string
        result: string
        detail: string
      }[]
      const entry = parsed.find((item) => item.id === task.id)
      if (!entry) {
        throw new Error(`check.py produced no result (exit ${result.exit}): ${(result.stdout + result.stderr).slice(-1500)}`)
      }
      if (entry.result === "PASS") {
        return { reasons: [] as Reason[], axioms: parseAxiomList(entry.detail), diagnostics: [] as string[] }
      }
      return {
        reasons: [{ code: checkPyReasonCode(entry.detail), message: entry.detail.slice(0, 4000) }],
        diagnostics: [] as string[],
      }
    } finally {
      await fs.rm(path.dirname(out), { recursive: true, force: true })
    }
  }

  function parseAxiomList(detail: string) {
    const match = /^axioms: (.*)$/.exec(detail)
    if (!match || match[1] === "none") return []
    return match[1].split(",").map((item) => item.trim())
  }

  /** The five checks on a candidate that is not (yet) the file on disk. */
  async function finalOnCandidate(
    root: string,
    input: FinalInput,
    statement: { text: string; universes: string[]; solution: string },
    settings: Config,
    frozenRoot: boolean,
  ): Promise<{ reasons: Reason[]; axioms?: string[]; diagnostics: string[] }> {
    let frozen: Frozen = { files: {}, closed_trees: [] }
    if (frozenRoot) {
      const checked = await frozenViolations(root)
      frozen = checked.frozen
      if (checked.bad.length) {
        return {
          reasons: [{ code: "FROZEN_CHANGED", message: "read-only files were changed or added: " + checked.bad.slice(0, 10).join("; ") }],
          diagnostics: [],
        }
      }
    }
    const helpers = frozenRoot ? await helperModules(root, input.candidateSource, frozen) : []
    const scanned: [string, string][] = [[input.file, input.candidateSource]]
    for (const module of helpers) {
      const file = LeanProject.moduleFile(root, module)
      const text = await Filesystem.readText(file).catch(() => undefined)
      if (text !== undefined) scanned.push([file, text])
    }
    for (const [file, text] of scanned) {
      const hits = LeanSource.forbiddenTokens(text)
      if (hits.length) {
        return {
          reasons: [{ code: "FORBIDDEN_TOKEN", file, message: `forbidden token(s) in ${path.relative(root, file)}: ${hits.join(", ")}` }],
          diagnostics: [],
        }
      }
    }
    if (helpers.length) {
      const built = await LeanProject.build(root, helpers, { timeoutMs: settings.timeoutMs, signal: input.signal })
      if (LeanProject.failed(built)) {
        const tail = (built.stdout + built.stderr).split("\n").filter((line) => line.includes("error")).join("\n").slice(0, 2000)
        return {
          reasons: [{ code: built.timedOut ? "BUILD_TIMEOUT" : "BUILD_FAILED", message: "helper modules failed to build" + (tail ? ": " + tail : "") }],
          diagnostics: [],
        }
      }
    }
    const uni = statement.universes.length ? `.{${statement.universes.join(", ")}}` : ""
    const universeLine = statement.universes.length ? `universe ${statement.universes.join(" ")}\n` : ""
    const probe =
      input.candidateSource.replace(/\s*$/, "\n\n") +
      universeLine +
      `theorem gate_check${uni} : ${statement.text}${uni} := ${statement.solution}\n\n` +
      "#print axioms gate_check\n"
    const { result, diagnostics } = await LeanProject.checkSource(root, input.file, probe, {
      timeoutMs: settings.timeoutMs,
      signal: input.signal,
    })
    const errors = diagnostics.filter((d) => d.severity === "error")
    if (result.timedOut) return { reasons: [{ code: "BUILD_TIMEOUT", message: "the solution did not elaborate in time" }], diagnostics: [] }
    if (errors.length || result.exit !== 0) {
      const candidateLines = input.candidateSource.split("\n").length
      const inProbe = errors.some((d) => d.line > candidateLines)
      const inSource = errors.filter((d) => d.line <= candidateLines)
      if (inSource.length) {
        return {
          reasons: inSource.slice(0, 5).map((d) => ({ code: "BUILD_FAILED", line: d.line, message: d.message.slice(0, 1000) })),
          diagnostics: [],
        }
      }
      return {
        reasons: [
          {
            code: inProbe ? "STATEMENT_MISMATCH" : "BUILD_FAILED",
            message:
              (inProbe ? "the solution does not prove the frozen statement: " : "elaboration failed: ") +
              (errors.map((d) => d.message).join("\n") || (result.stdout + result.stderr)).slice(0, 2000),
          },
        ],
        diagnostics: [],
      }
    }
    const axioms = parseAxioms(result.stdout + result.stderr)
    if (axioms === undefined) {
      return { reasons: [{ code: "AXIOMS_UNREADABLE", message: "could not read the axioms: " + (result.stdout + result.stderr).slice(0, 500) }], diagnostics: [] }
    }
    const extra = axioms.filter((axiom) => !LeanSource.ALLOWED_AXIOMS.includes(axiom)).sort()
    if (extra.length) return { reasons: [{ code: "AXIOMS", message: "uses non-standard axioms: " + extra.join(", ") }], axioms, diagnostics: [] }
    return { reasons: [], axioms, diagnostics: [] }
  }

  async function runFinal(input: FinalInput, settings: Config): Promise<Omit<Result, "stage" | "mode" | "status"> & { reasons: Reason[] }> {
    const bench = await benchmarkTask(input.file)
    if (bench) {
      const onDisk = await Filesystem.readText(input.file).catch(() => undefined)
      if (onDisk === input.candidateSource) {
        return { ...(await finalWithCheckPy(bench.root, bench.task, settings, input.signal)), method: "check.py", task: bench.task.id }
      }
      return {
        ...(await finalOnCandidate(
          bench.root,
          input,
          { text: bench.task.statement, universes: bench.task.universes, solution: bench.task.solution },
          settings,
          true,
        )),
        method: "benchmark",
        task: bench.task.id,
      }
    }
    const root = LeanProject.findRoot(input.file)
    if (!root) return { reasons: [{ code: "NO_LAKE_PROJECT", message: `no Lake project contains ${input.file}` }], diagnostics: [] }
    const baselineDecl = LeanSource.findDeclaration(input.baselineSource, input.theorem)
    const candidateDecl = LeanSource.findDeclaration(input.candidateSource, input.theorem)
    if (!baselineDecl || !candidateDecl) {
      return { reasons: [{ code: "TARGET_NOT_FOUND", message: `declaration ${input.theorem} not found` }], diagnostics: [], method: "general" }
    }
    const outside = exteriorChanges(input.baselineSource, input.candidateSource, input.theorem, settings)
    if (outside.length) return { reasons: outside, diagnostics: [], method: "general" }
    const proof = input.candidateSource.slice(candidateDecl.assign ?? candidateDecl.start, candidateDecl.end)
    const hits = LeanSource.forbiddenTokens(proof)
    if (hits.length) {
      return { reasons: [{ code: "FORBIDDEN_TOKEN", message: `forbidden token(s) in the proof of ${input.theorem}: ${hits.join(", ")}` }], diagnostics: [], method: "general" }
    }
    // The statement probe goes right after the target, in the same namespace/section context.
    const statementType = binderSignatureAsType(baselineDecl.signature)
    if (!statementType) {
      return { reasons: [{ code: "TARGET_NOT_FOUND", message: `the type of ${input.theorem} could not be read` }], diagnostics: [], method: "general" }
    }
    const probeSource =
      input.candidateSource.slice(0, candidateDecl.end).replace(/\s*$/, "\n\n") +
      `theorem gate_check : ${statementType} := ${candidateDecl.name}\n\n` +
      "#print axioms gate_check\n\n" +
      input.candidateSource.slice(candidateDecl.end)
    const { result, diagnostics } = await LeanProject.checkSource(root, input.file, probeSource, {
      timeoutMs: settings.timeoutMs,
      signal: input.signal,
    })
    const errors = diagnostics.filter((d) => d.severity === "error")
    if (errors.length || result.exit !== 0) {
      return {
        reasons: errors.length
          ? errors.slice(0, 5).map((d) => ({ code: "BUILD_FAILED", line: d.line, message: d.message.slice(0, 1000) }))
          : [{ code: result.timedOut ? "BUILD_TIMEOUT" : "BUILD_FAILED", message: (result.stdout + result.stderr).slice(0, 2000) }],
        diagnostics: [],
        method: "general",
      }
    }
    const axioms = parseAxioms(result.stdout + result.stderr)
    if (axioms === undefined) return { reasons: [{ code: "AXIOMS_UNREADABLE", message: "could not read the axioms" }], diagnostics: [], method: "general" }
    const extra = axioms.filter((axiom) => !LeanSource.ALLOWED_AXIOMS.includes(axiom))
    if (extra.length) return { reasons: [{ code: "AXIOMS", message: "uses non-standard axioms: " + extra.join(", ") }], axioms, diagnostics: [], method: "general" }
    return { reasons: [], axioms, diagnostics: [], method: "general" }
  }

  /**
   * `{α} (x : α) : P x` → `∀ {α} (x : α), P x` (the type of a declaration from its binders and result type).
   * Returns undefined when the signature has no binders (then it is `: T` and the type is `T`).
   */
  export function binderSignatureAsType(signature: string) {
    const code = LeanSource.blankComments(signature)
    let depth = 0
    for (let i = 0; i < code.length; i++) {
      const c = code[i]
      if ("([{⦃⟨".includes(c)) depth++
      else if (")]}⦄⟩".includes(c)) depth--
      else if (depth === 0 && c === ":" && code[i + 1] !== "=") {
        const binders = signature.slice(0, i).trim()
        const type = signature.slice(i + 1).trim()
        return binders ? `∀ ${binders}, ${type}` : type
      }
    }
    return undefined
  }

  // ---------------------------------------------------------------------------------------------------------
  // Submission stage and exterior comparison

  /**
   * Differences outside the target declaration's proof: the import header may only gain imports of the
   * configured package roots (K1); everything else must be unchanged, including the target's signature.
   */
  export function exteriorChanges(baseline: string, candidate: string, theorem: string, settings: Config = config()): Reason[] {
    const reasons: Reason[] = []
    const bh = LeanSource.header(baseline)
    const ch = LeanSource.header(candidate)
    const removed = bh.imports.filter((m) => !ch.imports.includes(m))
    if (removed.length) reasons.push({ code: "IMPORT_REMOVED", message: `imports removed: ${removed.join(", ")}` })
    const added = ch.imports.filter((m) => !bh.imports.includes(m))
    const foreign = added.filter((m) => !settings.importRoots.some((root) => m === root || m.startsWith(root + ".")))
    if (foreign.length) {
      reasons.push({
        code: "IMPORT_NOT_ALLOWED",
        message: `only modules of this package (${settings.importRoots.join(", ")}) may be imported: ${foreign.join(", ")}`,
      })
    }
    const bBody = baseline.slice(bh.bodyOffset)
    const cBody = candidate.slice(ch.bodyOffset)
    const bd = LeanSource.findDeclaration(bBody, theorem)
    const cd = LeanSource.findDeclaration(cBody, theorem)
    if (!bd || !cd || bd.assign === undefined || cd.assign === undefined) {
      reasons.push({ code: "TARGET_NOT_FOUND", message: `the proof of ${theorem} could not be located` })
      return reasons
    }
    const norm = (text: string) => text.replace(/\s+$/g, "")
    if (norm(bBody.slice(0, bd.assign)) !== norm(cBody.slice(0, cd.assign))) {
      reasons.push({
        code: "REGION_OUTSIDE_EDIT",
        line: ch.bodyLine + firstDifferenceLine(bBody.slice(0, bd.assign), cBody.slice(0, cd.assign)),
        message: `text before the proof of ${theorem} (declarations above it or its statement) was changed`,
      })
    }
    if (norm(bBody.slice(bd.end)) !== norm(cBody.slice(cd.end))) {
      reasons.push({
        code: "REGION_OUTSIDE_EDIT",
        line: ch.bodyLine + cBody.slice(0, cd.end).split("\n").length + firstDifferenceLine(bBody.slice(bd.end), cBody.slice(cd.end)) - 1,
        message: `text after the proof of ${theorem} was changed`,
      })
    }
    return reasons
  }

  function firstDifferenceLine(a: string, b: string) {
    const al = a.split("\n")
    const bl = b.split("\n")
    for (let i = 0; i < Math.max(al.length, bl.length); i++) if (al[i] !== bl[i]) return i + 1
    return 1
  }

  async function runSubmission(
    input: FinalInput & { allowSorry: boolean },
    settings: Config,
  ): Promise<{ reasons: Reason[]; diagnostics: string[] }> {
    const outside = exteriorChanges(input.baselineSource, input.candidateSource, input.theorem, settings)
    if (outside.length) return { reasons: outside, diagnostics: [] }
    const head = LeanSource.header(input.candidateSource)
    const body = input.candidateSource.slice(head.bodyOffset)
    const decl = LeanSource.findDeclaration(body, input.theorem)!
    const proof = body.slice(decl.assign!, decl.end)
    const hits = LeanSource.forbiddenTokens(proof, input.allowSorry ? ["sorry"] : [])
    if (hits.length) return { reasons: [{ code: "FORBIDDEN_TOKEN", message: `forbidden token(s) in the proof: ${hits.join(", ")}` }], diagnostics: [] }
    const root = LeanProject.findRoot(input.file)
    if (!root) return { reasons: [{ code: "NO_LAKE_PROJECT", message: `no Lake project contains ${input.file}` }], diagnostics: [] }
    const { result, diagnostics } = await LeanProject.checkSource(root, input.file, input.candidateSource, {
      timeoutMs: settings.timeoutMs,
      signal: input.signal,
    })
    if (result.timedOut) return { reasons: [{ code: "REGION_CHECK_TIMEOUT", message: "the file did not elaborate in time" }], diagnostics: [] }
    const declStartLine = head.bodyLine + body.slice(0, decl.start).split("\n").length
    const declEndLine = head.bodyLine + body.slice(0, decl.end).split("\n").length
    const errors = diagnostics.filter((d) => d.severity === "error")
    const inTarget = errors.filter((d) => d.line >= declStartLine && d.line <= declEndLine)
    if (inTarget.length) {
      return {
        reasons: inTarget.slice(0, 5).map((d) => ({ code: "REGION_DOES_NOT_ELABORATE", line: d.line, message: d.message.slice(0, 1000) })),
        diagnostics: [],
      }
    }
    return { reasons: [], diagnostics: errors.map((d) => `${d.line}:${d.column}: ${d.message}`) }
  }

  // ---------------------------------------------------------------------------------------------------------
  // Entry points

  export async function run(input: {
    file: string
    theorem: string
    baselineSource: string
    candidateSource: string
    stage: Stage
    signal?: AbortSignal
    transactionID?: string
    /** Submission stage: `sorry` may remain in the proof (a split). Default false. */
    allowSorry?: boolean
  }): Promise<Result> {
    const settings = config()
    const base = {
      stage: input.stage,
      mode: settings.mode,
      theorem: input.theorem,
      baseline_hash: hash(input.baselineSource),
      candidate_hash: hash(input.candidateSource),
      transaction_id: input.transactionID,
    }
    if (settings.mode === "off") {
      return { ...base, status: "disabled", reasons: [{ code: "GATE_DISABLED", message: "The Lean gate is disabled by OPENCODE_LEAN_GATE=off." }], diagnostics: [] }
    }
    try {
      const outcome =
        input.stage === "final"
          ? await runFinal(input, settings)
          : await runSubmission({ ...input, allowSorry: input.allowSorry ?? false }, settings)
      return { ...base, ...outcome, status: outcome.reasons.length ? "rejected" : "accepted" }
    } catch (error) {
      return {
        ...base,
        status: "error",
        reasons: [{ code: "GATE_EXECUTION_FAILED", message: error instanceof Error ? error.message : String(error) }],
        diagnostics: [],
      }
    }
  }

  export async function runForSession(input: {
    sessionID: string
    file: string
    candidateSource: string
    theorem?: string
    stage: Stage
    signal?: AbortSignal
    allowSorry?: boolean
  }): Promise<Result> {
    const settings = config()
    const transaction = ProofEditTransaction.auditContext(input.sessionID, input.file)
    const binding = SessionProof.get(input.sessionID)
    const bindingMatches = binding && path.normalize(binding.file) === path.normalize(input.file)
    const baselineSource = transaction?.baselineSource ?? (bindingMatches ? binding.canonicalSource : undefined)
    const theorem = input.theorem ?? transaction?.theorem
    if (settings.mode === "off" || baselineSource === undefined || !theorem) {
      const status = settings.mode === "off" ? "disabled" : settings.mode === "required" ? "error" : "disabled"
      return {
        status,
        stage: input.stage,
        mode: settings.mode,
        theorem,
        reasons: [
          settings.mode === "off"
            ? { code: "GATE_DISABLED", message: "The Lean gate is disabled by OPENCODE_LEAN_GATE=off." }
            : { code: "GATE_BASELINE_UNAVAILABLE", message: "No original proof source and theorem identity are bound to this session." },
        ],
        diagnostics: [],
        candidate_hash: hash(input.candidateSource),
        transaction_id: transaction?.transactionID,
      }
    }
    return run({
      file: input.file,
      theorem,
      baselineSource,
      candidateSource: input.candidateSource,
      stage: input.stage,
      signal: input.signal,
      transactionID: transaction?.transactionID,
      allowSorry: input.allowSorry,
    })
  }
}
