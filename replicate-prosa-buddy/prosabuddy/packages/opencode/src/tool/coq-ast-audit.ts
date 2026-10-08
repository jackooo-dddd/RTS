import fs from "fs/promises"
import os from "os"
import path from "path"
import { createHash } from "crypto"
import { SessionProof } from "@/session/session-proof"
import { ProofEditTransaction } from "@/session/proof-edit-transaction"
import { which } from "@/util/which"
import * as CoqProject from "./coq-project"

export namespace CoqAstAudit {
  export type Stage = "submission" | "final"
  export type Mode = "off" | "auto" | "required"

  export type Reason = {
    code: string
    message: string
    file?: string
    index?: number
    line?: number
    details?: Record<string, unknown>
  }

  export type Result = {
    status: "accepted" | "rejected" | "error" | "disabled"
    stage: Stage
    mode: Mode
    theorem?: string
    reasons: Reason[]
    allowed_additions: unknown[]
    diagnostics: string[]
    baseline_hash?: string
    candidate_hash?: string
    transaction_id?: string
  }

  export type Config = {
    mode: Mode
    timeoutMs: number
    trustedRequireRoots: Set<string>
    trustedPlugins: string[]
    fcc: string | null
    python: string | null
    classifier: string
    validator: string
  }

  type ClassifiedRecord = {
    phase?: unknown
    vernac_kind?: unknown
    require?: unknown
  }

  const DEFAULT_TIMEOUT_MS = 120_000
  const DEFAULT_TRUSTED_REQUIRE_ROOTS = ["mathcomp", "prosa"]

  function positiveInteger(raw: string | undefined, fallback: number) {
    if (!raw) return fallback
    const parsed = Number.parseInt(raw, 10)
    return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback
  }

  function csv(raw: string | undefined, fallback: string[]) {
    return (raw === undefined ? fallback : raw.split(","))
      .map((item) => item.trim())
      .filter(Boolean)
  }

  function mode(): Mode {
    const raw = process.env.OPENCODE_COQ_AST_AUDIT?.trim().toLowerCase()
    if (!raw) return "auto"
    if (raw === "off" || raw === "auto" || raw === "required") return raw
    // Invalid security configuration must not silently disable the gate.
    return "required"
  }

  function repositoryScriptsDirectory() {
    return path.resolve(import.meta.dirname, "../../../../scripts")
  }

  export function config(): Config {
    const scripts = repositoryScriptsDirectory()
    return {
      mode: mode(),
      timeoutMs: positiveInteger(process.env.OPENCODE_COQ_AST_AUDIT_TIMEOUT_MS, DEFAULT_TIMEOUT_MS),
      trustedRequireRoots: new Set(
        csv(process.env.OPENCODE_COQ_AST_TRUSTED_REQUIRE_ROOTS, DEFAULT_TRUSTED_REQUIRE_ROOTS),
      ),
      trustedPlugins: csv(process.env.OPENCODE_COQ_AST_TRUSTED_PLUGINS, []),
      fcc: process.env.OPENCODE_COQ_AST_FCC?.trim() || which("fcc"),
      python: process.env.OPENCODE_COQ_AST_PYTHON?.trim() || which("python3"),
      classifier:
        process.env.OPENCODE_COQ_AST_CLASSIFIER?.trim() || path.join(scripts, "classify_vernac_ast"),
      validator:
        process.env.OPENCODE_COQ_AST_VALIDATOR?.trim() || path.join(scripts, "validate_classified_ast.py"),
    }
  }

  export function maxSubmissionRepairs() {
    return positiveInteger(process.env.OPENCODE_COQ_AST_AUDIT_MAX_REPAIRS, 2)
  }

  function hash(source: string) {
    return createHash("sha256").update(source).digest("hex")
  }

  function unavailable(input: {
    stage: Stage
    config: Config
    theorem?: string
    code: string
    message: string
    baselineSource?: string
    candidateSource?: string
    transactionID?: string
  }): Result {
    const status = input.config.mode === "off"
      ? "disabled"
      : input.config.mode === "required" || (input.baselineSource !== undefined && input.theorem)
        ? "error"
        : "disabled"
    return {
      status,
      stage: input.stage,
      mode: input.config.mode,
      theorem: input.theorem,
      reasons: [{ code: input.code, message: input.message }],
      allowed_additions: [],
      diagnostics: [],
      baseline_hash: input.baselineSource ? hash(input.baselineSource) : undefined,
      candidate_hash: input.candidateSource ? hash(input.candidateSource) : undefined,
      transaction_id: input.transactionID,
    }
  }

  function failure(input: {
    stage: Stage
    config: Config
    theorem: string
    code: string
    message: string
    baselineSource: string
    candidateSource: string
    diagnostics?: string[]
    transactionID?: string
  }): Result {
    return {
      status: "error",
      stage: input.stage,
      mode: input.config.mode,
      theorem: input.theorem,
      reasons: [{ code: input.code, message: input.message }],
      allowed_additions: [],
      diagnostics: input.diagnostics ?? [],
      baseline_hash: hash(input.baselineSource),
      candidate_hash: hash(input.candidateSource),
      transaction_id: input.transactionID,
    }
  }

  async function executable(pathname: string | null) {
    if (!pathname) return false
    try {
      await fs.access(pathname)
      return true
    } catch {
      return false
    }
  }

  function processDiagnostic(label: string, result: CoqProject.ProcessResult) {
    const flags = [
      result.timedOut ? "timed out" : "",
      result.aborted ? "aborted" : "",
      result.outputLimitExceeded ? "output limit exceeded" : "",
      result.exit !== 0 ? `exit ${result.exit}` : "",
    ].filter(Boolean)
    const output = [result.stdout.trim(), result.stderr.trim()].filter(Boolean).join("\n")
    return `${label}: ${flags.join(", ") || "failed"}${output ? `\n${output}` : ""}`
  }

  async function runChecked(
    label: string,
    args: string[],
    cwd: string,
    config: Config,
    signal?: AbortSignal,
  ) {
    const result = await CoqProject.runProcess(args, cwd, {
      timeoutMs: config.timeoutMs,
      signal,
    })
    if (
      result.exit !== 0 ||
      result.timedOut ||
      result.aborted ||
      result.outputLimitExceeded
    ) {
      throw new Error(processDiagnostic(label, result))
    }
    return result
  }

  function logicalRoot(fromPrefix: string | null, module: string) {
    const value = fromPrefix ?? module
    return value.split(".", 1)[0]
  }

  function requireKey(fromPrefix: string | null, module: string) {
    return fromPrefix ? `${fromPrefix}::${module}` : module
  }

  export function trustedRequireKeys(records: ClassifiedRecord[], roots: Set<string>) {
    const keys = new Set<string>()
    for (const record of records) {
      if (record.phase !== "VernacSynterp" || record.vernac_kind !== "VernacRequire") continue
      const require = record.require
      if (!require || typeof require !== "object" || Array.isArray(require)) continue
      const fromValue = "from" in require ? require.from : undefined
      const fromPrefix = fromValue === null || typeof fromValue === "string" ? fromValue : undefined
      if (fromPrefix === undefined) continue
      const modules = "modules" in require ? require.modules : undefined
      if (!Array.isArray(modules)) continue
      for (const item of modules) {
        if (!item || typeof item !== "object" || Array.isArray(item) || !("name" in item)) continue
        const module = item.name
        if (typeof module !== "string") continue
        if (!roots.has(logicalRoot(fromPrefix, module))) continue
        keys.add(requireKey(fromPrefix, module))
      }
    }
    return [...keys].sort()
  }

  async function readJsonLines(file: string): Promise<ClassifiedRecord[]> {
    const text = await fs.readFile(file, "utf8")
    return text
      .split("\n")
      .filter((line) => line.trim())
      .map((line) => JSON.parse(line) as ClassifiedRecord)
  }

  function parseVerdict(stdout: string) {
    const parsed = JSON.parse(stdout) as {
      accepted?: unknown
      rejected?: unknown
      reasons?: unknown
      allowed_additions?: unknown
    }
    if (typeof parsed.accepted !== "boolean" || !Array.isArray(parsed.reasons)) {
      throw new Error("validator output does not match the expected verdict schema")
    }
    return {
      accepted: parsed.accepted,
      reasons: parsed.reasons as Reason[],
      allowed_additions: Array.isArray(parsed.allowed_additions) ? parsed.allowed_additions : [],
    }
  }

  export async function run(input: {
    file: string
    theorem: string
    baselineSource: string
    candidateSource: string
    stage: Stage
    signal?: AbortSignal
    extraFlags?: string[]
    transactionID?: string
  }): Promise<Result> {
    const settings = config()
    const common = {
      stage: input.stage,
      config: settings,
      theorem: input.theorem,
      baselineSource: input.baselineSource,
      candidateSource: input.candidateSource,
      transactionID: input.transactionID,
    }
    if (settings.mode === "off") {
      return unavailable({
        ...common,
        code: "AST_AUDIT_DISABLED",
        message: "Rocq AST audit is disabled by OPENCODE_COQ_AST_AUDIT=off.",
      })
    }

    const missing = [
      !(await executable(settings.fcc)) ? "fcc" : "",
      !(await executable(settings.python)) ? "python3" : "",
      !(await executable(settings.classifier)) ? settings.classifier : "",
      !(await executable(settings.validator)) ? settings.validator : "",
    ].filter(Boolean)
    if (missing.length) {
      return unavailable({
        ...common,
        code: "AST_AUDIT_TOOLING_UNAVAILABLE",
        message: `Rocq AST audit tooling is unavailable: ${missing.join(", ")}.`,
      })
    }

    const tempRoot = await fs.mkdtemp(path.join(os.tmpdir(), "prosabuddy-ast-audit-"))
    try {
      // Use a stable Rocq-valid module filename. The workspace source may have
      // spaces or punctuation that fcc rejects as a compilation-unit name.
      const basename = "input.v"
      const originalDirectory = path.join(tempRoot, "original")
      const candidateDirectory = path.join(tempRoot, "candidate")
      await fs.mkdir(originalDirectory)
      await fs.mkdir(candidateDirectory)
      const originalFile = path.join(originalDirectory, basename)
      const candidateFile = path.join(candidateDirectory, basename)
      await fs.writeFile(originalFile, input.baselineSource, "utf8")
      await fs.writeFile(candidateFile, input.candidateSource, "utf8")

      const resolved = await CoqProject.resolve(input.file)
      const flags = [...resolved.flags, ...(input.extraFlags ?? [])]
      const fcc = settings.fcc!
      await runChecked(
        "baseline astdump",
        [fcc, "--no_vo", "--plugin=coq-lsp.plugin.astdump", ...flags, originalFile],
        resolved.cwd,
        settings,
        input.signal,
      )
      await runChecked(
        "candidate astdump",
        [fcc, "--no_vo", "--plugin=coq-lsp.plugin.astdump", ...flags, candidateFile],
        resolved.cwd,
        settings,
        input.signal,
      )

      const originalDump = `${originalFile}.jsonl.astdump`
      const candidateDump = `${candidateFile}.jsonl.astdump`
      const originalClassified = `${originalFile}.classified.jsonl`
      const candidateClassified = `${candidateFile}.classified.jsonl`
      await runChecked(
        "baseline AST classification",
        [settings.classifier, originalDump, originalClassified],
        resolved.cwd,
        settings,
        input.signal,
      )
      await runChecked(
        "candidate AST classification",
        [settings.classifier, candidateDump, candidateClassified],
        resolved.cwd,
        settings,
        input.signal,
      )

      const candidateRecords = await readJsonLines(candidateClassified)
      const allowedRequires = trustedRequireKeys(candidateRecords, settings.trustedRequireRoots)
      const validatorArgs = [
        settings.python!,
        settings.validator,
        originalClassified,
        candidateClassified,
        "--target",
        input.theorem,
        "--stage",
        input.stage,
        "--allow-query",
        "--compact",
        ...allowedRequires.flatMap((item) => ["--allow-require", item]),
        ...settings.trustedPlugins.flatMap((item) => ["--trusted-plugin", item]),
      ]
      const validator = await CoqProject.runProcess(validatorArgs, resolved.cwd, {
        timeoutMs: settings.timeoutMs,
        signal: input.signal,
      })
      if (validator.timedOut || validator.aborted || validator.outputLimitExceeded || validator.exit > 1) {
        throw new Error(processDiagnostic("classified AST validation", validator))
      }
      const verdict = parseVerdict(validator.stdout)
      return {
        status: verdict.accepted ? "accepted" : "rejected",
        stage: input.stage,
        mode: settings.mode,
        theorem: input.theorem,
        reasons: verdict.reasons,
        allowed_additions: verdict.allowed_additions,
        diagnostics: validator.stderr.trim() ? [validator.stderr.trim()] : [],
        baseline_hash: hash(input.baselineSource),
        candidate_hash: hash(input.candidateSource),
        transaction_id: input.transactionID,
      }
    } catch (error) {
      return failure({
        ...common,
        code: "AST_AUDIT_EXECUTION_FAILED",
        message: error instanceof Error ? error.message : String(error),
      })
    } finally {
      await fs.rm(tempRoot, { recursive: true, force: true })
    }
  }

  export async function runForSession(input: {
    sessionID: string
    file: string
    candidateSource: string
    theorem?: string
    stage: Stage
    signal?: AbortSignal
    extraFlags?: string[]
  }): Promise<Result> {
    const settings = config()
    if (settings.mode === "off") {
      return unavailable({
        stage: input.stage,
        config: settings,
        theorem: input.theorem,
        code: "AST_AUDIT_DISABLED",
        message: "Rocq AST audit is disabled by OPENCODE_COQ_AST_AUDIT=off.",
        candidateSource: input.candidateSource,
      })
    }

    const transaction = ProofEditTransaction.auditContext(input.sessionID, input.file)
    const binding = SessionProof.get(input.sessionID)
    const bindingMatches = binding && path.normalize(binding.file) === path.normalize(input.file)
    const baselineSource = transaction?.baselineSource ?? (bindingMatches ? binding.canonicalSource : undefined)
    const theorem = input.theorem ?? transaction?.theorem
    if (baselineSource === undefined || !theorem) {
      return unavailable({
        stage: input.stage,
        config: settings,
        theorem,
        code: "AST_AUDIT_BASELINE_UNAVAILABLE",
        message: "No immutable original proof source and theorem identity are bound to this session.",
        baselineSource,
        candidateSource: input.candidateSource,
        transactionID: transaction?.transactionID,
      })
    }
    return run({
      file: input.file,
      theorem,
      baselineSource,
      candidateSource: input.candidateSource,
      stage: input.stage,
      signal: input.signal,
      extraFlags: input.extraFlags,
      transactionID: transaction?.transactionID,
    })
  }

  export function passed(result: Result) {
    return result.status === "accepted" || result.status === "disabled"
  }

  export function formatReasons(result: Result) {
    return result.reasons.map((reason) => {
      const location = reason.line ? ` line ${reason.line}` : reason.index ? ` command ${reason.index}` : ""
      return `- [${reason.code}]${location}: ${reason.message}`
    })
  }
}
