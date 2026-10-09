import z from "zod"
import { Tool } from "./tool"
import DESCRIPTION from "./lean-check.txt"
import { Instance } from "../project/instance"
import path from "path"
import { Filesystem } from "../util/filesystem"
import { formatCoqSkillHints } from "./coq-skill-hints"
import { SessionProofWorkflow } from "@/session/proof-workflow"
import { ProofEditTransaction } from "@/session/proof-edit-transaction"
import { LeanGate } from "./lean-gate"
import { LeanProject } from "./lean-project"

function formatMs(ms: number) {
  if (ms % 1000 === 0) return `${ms / 1000}s`
  return `${ms}ms`
}

/** `lean_check`: elaborate the staged revision of a `.lean` file with the project's Lean (DECISIONS D2). */
export const LeanCheckTool = Tool.define("lean_check", {
  description: DESCRIPTION,
  parameters: z.object({
    filePath: z.string().describe("Path to the .lean file to check (its staged revision is checked)"),
  }),
  async execute(params, ctx): Promise<{ title: string; output: string; metadata: Record<string, any> }> {
    let filepath = params.filePath
    if (!path.isAbsolute(filepath)) {
      filepath = path.resolve(Instance.directory, filepath)
    }

    if (!Filesystem.contains(Instance.directory, filepath)) {
      throw new Error(`File must be within workspace: ${Instance.directory}`)
    }

    if (!filepath.endsWith(".lean")) {
      throw new Error("File must be a .lean (Lean source) file")
    }

    const stat = Filesystem.stat(filepath)
    if (!stat) throw new Error(`File not found: ${filepath}`)

    const stagedTransaction = ProofEditTransaction.isTarget(ctx.sessionID, filepath)
    const stagedSource = await ProofEditTransaction.readSource(ctx.sessionID, filepath)

    await ctx.ask({
      permission: "lean_check",
      patterns: [filepath],
      always: ["*"],
      metadata: { filepath },
    })

    const timeoutMs = LeanProject.timeoutMs()
    const compiled = await LeanProject.compile(filepath, stagedSource, { timeoutMs, signal: ctx.abort })
    const code = compiled.ok ? 0 : 1
    const stdout = compiled.output
    const stderr = ""
    const timedOut = compiled.timedOut
    const aborted = compiled.aborted
    const outputLimitExceeded = compiled.outputLimitExceeded

    const rel = path.relative(Instance.directory, filepath)

    if (timedOut) {
      const partial = [
        stdout.trim() ? `partial stdout:\n${stdout.trim()}` : "",
        stderr.trim() ? `partial stderr:\n${stderr.trim()}` : "",
      ]
        .filter(Boolean)
        .join("\n")
      throw new Error(
        [`lean_check timed out after ${formatMs(timeoutMs)} while checking ${rel}; process group was killed.`, partial]
          .filter(Boolean)
          .join("\n"),
      )
    }
    if (aborted) throw new Error(`lean_check was aborted while checking ${rel}; process group was killed.`)
    if (outputLimitExceeded) {
      throw new Error(
        `lean_check exceeded the output limit while checking ${rel}; process group was killed.`,
      )
    }

    if (code === 0) {
      const finalPreview = SessionProofWorkflow.previewFinalTheoremGate(ctx.sessionID, filepath, stagedSource)
      const finalGate = finalPreview.final_theorem_gate.ok
        ? await LeanGate.runForSession({
            sessionID: ctx.sessionID,
            file: filepath,
            candidateSource: stagedSource,
            theorem: finalPreview.theorem,
            stage: "final",
            signal: ctx.abort,
          })
        : undefined
      if (finalGate && !LeanGate.passed(finalGate)) {
        return {
          title: `lean_check ${rel}: final gate rejected`,
          output: [
            "status: final_gate_rejected",
            "compile_status: success",
            "status_detail: final_theorem_gate_rejected",
            finalPreview.theorem ? `theorem: ${finalPreview.theorem}` : undefined,
            "final_theorem_gate: the file checks, but the final gate failed (see the reason codes below)",
            ...LeanGate.formatReasons(finalGate),
            "next_action: the main prover must repair the current staged proof revision and run lean_check again; this revision was not marked committable and was not finalized",
          ].filter((line): line is string => Boolean(line)).join("\n"),
          metadata: {
            status: "final_gate_rejected",
            status_detail: "final_theorem_gate_rejected",
            filepath,
            errors: finalGate.reasons.map((reason) => ({
              line: reason.line ?? 0,
              message: `[${reason.code}] ${reason.message}`,
            })),
            final_theorem_gate: finalPreview.final_theorem_gate,
            final_gate: finalGate,
          },
        }
      }
      if (finalGate) {
        ProofEditTransaction.markGateChecked({
          sessionID: ctx.sessionID,
          file: filepath,
          source: stagedSource,
        })
      }
      const lemmaPrefixValidation = await SessionProofWorkflow.recordLemmaPrefixValidation({
        sessionID: ctx.sessionID,
        agent: ctx.agent,
        file: filepath,
        source: stagedSource,
      })
      const proofRegionLifecycle = await SessionProofWorkflow.recordCompilerResult({
        sessionID: ctx.sessionID,
        file: filepath,
        source: stagedSource,
        validator: "lean_check",
        ok: true,
        validated_source_current: stagedTransaction,
      })
      const proofStatus = SessionProofWorkflow.classifyCompileSuccess(
        ctx.sessionID,
        filepath,
        stagedSource,
        proofRegionLifecycle,
      )
      const decompositionCheckpoint = SessionProofWorkflow.decompositionModeEnabled()
        ? SessionProofWorkflow.classifyDecompositionCheckpoint(ctx.sessionID, filepath, stagedSource)
        : undefined
      const proofStatusMetadata: unknown = proofStatus
      const statusDetail: string = proofStatus.status_detail
      let proofTransaction = proofStatus.proof_progress.workspace_committable
        ? ProofEditTransaction.markAccepted({
            sessionID: ctx.sessionID,
            file: filepath,
            source: stagedSource,
            level: proofStatus.proof_progress.level === "structural" ? "structural" : "hard",
            receipt: proofStatus.proof_progress.receipt,
          })
        : proofStatus.proof_progress.accepted &&
            (proofStatus.proof_progress.level === "hard" || proofStatus.proof_progress.level === "structural")
          ? ProofEditTransaction.markCertifiedRecovery({
              sessionID: ctx.sessionID,
              file: filepath,
              source: stagedSource,
              level: proofStatus.proof_progress.level,
              receipt: proofStatus.proof_progress.receipt,
            })
        : proofStatus.proof_progress.level === "debug"
          ? ProofEditTransaction.markDebug({
              sessionID: ctx.sessionID,
              file: filepath,
              source: stagedSource,
              receipt: proofStatus.proof_progress.receipt,
            })
          : ProofEditTransaction.active(ctx.sessionID)
      if (proofStatus.final_theorem_gate.ok && proofStatus.proof_progress.workspace_committable) {
        proofTransaction =
          (await ProofEditTransaction.finalizeHandedOffAccepted(ctx.sessionID, { requireGate: true })) ?? proofTransaction
      }
      const toolStatus = decompositionCheckpoint
        ? decompositionCheckpoint.terminal_ready
          ? "decomposition_ready"
          : "decomposition_incomplete"
        : "success"
      return {
        title: `lean_check ${rel}: ${decompositionCheckpoint ? toolStatus : statusDetail}`,
        output: [
          `status: ${toolStatus}`,
          decompositionCheckpoint ? "compile_status: success" : undefined,
          decompositionCheckpoint ? `decomposition_status: ${decompositionCheckpoint.status}` : undefined,
          decompositionCheckpoint ? `terminal_ready: ${decompositionCheckpoint.terminal_ready}` : undefined,
          `status_detail: ${statusDetail}`,
          proofStatus.theorem ? `theorem: ${proofStatus.theorem}` : undefined,
          `has_unfinished_proof: ${proofStatus.has_unfinished_proof}`,
          `proof_progress: ${proofStatus.proof_progress.status}`,
          `progress_level: ${proofStatus.proof_progress.level ?? "none"}`,
          `accepted_progress: ${proofStatus.proof_progress.accepted}`,
          `unfinished_count: ${proofStatus.proof_progress.current.unfinished_count}`,
          proofStatus.proof_progress.previous
            ? `previous_unfinished_count: ${proofStatus.proof_progress.previous.unfinished_count}`
            : undefined,
          `proof_progress_reason: ${proofStatus.proof_progress.reason}`,
          stagedTransaction
            ? `proof_transaction: ${proofStatus.proof_progress.workspace_committable ? `${proofStatus.proof_progress.level} snapshot updated` : "debug draft journaled for further repair"}`
            : undefined,
          proofStatus.final_theorem_gate.ok
            ? "final_theorem_gate: ok"
            : `final_theorem_gate: fail - ${proofStatus.final_theorem_gate.reason}`,
          finalGate ? `final_gate: ${finalGate.status}` : undefined,
          lemmaPrefixValidation?.ok
            ? `lemma_prefix_validation: ok - ${lemmaPrefixValidation.prefix_complete ? "current blocker complete" : lemmaPrefixValidation.message ?? "current prefix compiles but current blocker is still pending"}`
            : lemmaPrefixValidation
              ? `lemma_prefix_validation: fail - ${lemmaPrefixValidation.message ?? "prefix checkpoint failed"}`
              : undefined,
          `proof_region_lifecycle: ${JSON.stringify(proofRegionLifecycle)}`,
          decompositionCheckpoint
            ? `decomposition_checkpoint: ${JSON.stringify(decompositionCheckpoint)}`
            : undefined,
          statusDetail === "compile_success_nonfinal" && !proofStatus.proof_progress.accepted
            ? "next_action: this check is not accepted proof progress; obtain a new proof_region certificate or complete the theorem without `sorry`"
            : undefined,
          compiled.sorries.length ? `unfinished: ${compiled.sorries.length} declaration(s) use \`sorry\` (lines ${compiled.sorries.map((d) => d.line).join(", ")})` : undefined,
          compiled.warnings.length > compiled.sorries.length ? `warnings: ${compiled.warnings.length - compiled.sorries.length}` : undefined,
        ].filter((line): line is string => Boolean(line)).join("\n"),
        metadata: {
          status: toolStatus,
          ...(decompositionCheckpoint
            ? {
                compile_status: "success",
                decomposition_status: decompositionCheckpoint.status,
                terminal_ready: decompositionCheckpoint.terminal_ready,
                decomposition_checkpoint: decompositionCheckpoint,
              }
            : {}),
          status_detail: statusDetail,
          filepath,
          errors: [] as { line: number; message: string }[],
          proof_status: proofStatusMetadata,
          proof_region_lifecycle: proofRegionLifecycle,
          ...(finalGate ? { final_gate: finalGate } : {}),
          ...(proofTransaction ? { proof_edit_transaction: proofTransaction } : {}),
          ...(lemmaPrefixValidation ? { lemma_prefix_validation: lemmaPrefixValidation } : {}),
        },
      }
    }

    const firstError = compiled.errors[0]
    const diagnostics = {
      firstError: firstError ? { severity: "error", file: filepath, line: firstError.line, message: firstError.message } : undefined,
      errors: compiled.errors.map((error) => ({ severity: "error", file: filepath, line: error.line, message: error.message })),
      output: compiled.helperFailure ? `helper module build failed:\n${compiled.helperFailure}` : compiled.output.slice(-4000),
    }
    const proofRegionLifecycle = await SessionProofWorkflow.recordCompilerResult({
      sessionID: ctx.sessionID,
      file: filepath,
      source: stagedSource,
      validator: "lean_check",
      ok: false,
      first_error_file: diagnostics.firstError?.file,
      first_error_line: diagnostics.firstError?.line,
      first_error_message: diagnostics.firstError?.message,
      error_lines: compiled.errors.map((error) => error.line),
      validated_source_current: stagedTransaction,
    })
    const proofStatus = SessionProofWorkflow.classifyCompileFailure(ctx.sessionID, filepath, stagedSource, {
      first_error_line: diagnostics.firstError?.line,
      first_error_message: diagnostics.firstError?.message,
      lifecycle: proofRegionLifecycle,
    })
    const proofTransaction = proofStatus.proof_progress.accepted &&
        (proofStatus.proof_progress.level === "hard" || proofStatus.proof_progress.level === "structural")
      ? ProofEditTransaction.markCertifiedRecovery({
          sessionID: ctx.sessionID,
          file: filepath,
          source: stagedSource,
          level: proofStatus.proof_progress.level,
          receipt: proofStatus.proof_progress.receipt,
        })
      : proofStatus.proof_progress.level === "debug"
        ? ProofEditTransaction.markDebug({
            sessionID: ctx.sessionID,
            file: filepath,
            source: stagedSource,
            receipt: proofStatus.proof_progress.receipt,
          })
        : ProofEditTransaction.active(ctx.sessionID)
    const lemmaPrefixValidation = await SessionProofWorkflow.recordLemmaPrefixValidation({
      sessionID: ctx.sessionID,
      agent: ctx.agent,
      file: filepath,
      source: stagedSource,
    })
    const errors = diagnostics.errors.map((error) => ({ line: error.line ?? 0, message: error.message }))

    const summary = errors.length > 0
      ? errors.map((e) => `line ${e.line}: ${e.message}`).join("\n---\n")
      : diagnostics.output

    return {
      title: `lean_check ${rel}: ${lemmaPrefixValidation?.ok ? "lemma-prefix-ok" : "fail"}`,
      output: [
        "status: fail",
        lemmaPrefixValidation?.ok
          ? `lemma_prefix_validation: ok - ${lemmaPrefixValidation.prefix_complete ? "current blocker complete" : lemmaPrefixValidation.message ?? "current prefix compiles but current blocker is still pending"}`
          : lemmaPrefixValidation
            ? `lemma_prefix_validation: fail - ${lemmaPrefixValidation.message ?? "prefix checkpoint failed"}`
            : undefined,
        lemmaPrefixValidation?.ok && lemmaPrefixValidation.prefix_complete
          ? "next_action: advance to the next local proof hole toward completing the target theorem; keep later proof regions intact"
          : lemmaPrefixValidation
            ? "next_action: repair the current first proof block with an edit toward a compiling theorem proof; do not switch to broad read-only search or unrelated edits"
            : undefined,
        `proof_region_lifecycle: ${JSON.stringify(proofRegionLifecycle)}`,
        `proof_progress: ${proofStatus.proof_progress.status}`,
        `progress_level: ${proofStatus.proof_progress.level ?? "none"}`,
        `accepted_progress: ${proofStatus.proof_progress.accepted}`,
        `proof_progress_reason: ${proofStatus.proof_progress.reason}`,
        stagedTransaction
          ? `proof_transaction: ${proofStatus.proof_progress.workspace_committable ? `${proofStatus.proof_progress.level} snapshot updated` : "debug draft journaled for further repair"}`
          : undefined,
        `errors:\n${summary}${formatCoqSkillHints(summary)}`,
      ].filter((line): line is string => Boolean(line)).join("\n"),
      metadata: {
        status: "fail",
        status_detail: lemmaPrefixValidation?.ok && lemmaPrefixValidation.prefix_complete ? "lemma_prefix_success_full_compile_failed" : "compile_failed",
        filepath,
        errors,
        proof_status: proofStatus,
        proof_region_lifecycle: proofRegionLifecycle,
        ...(proofTransaction ? { proof_edit_transaction: proofTransaction } : {}),
        ...(lemmaPrefixValidation ? { lemma_prefix_validation: lemmaPrefixValidation } : {}),
      },
    }
  },
})
