import { which } from "./which"

/** Bounded subprocesses (Lean, Lake): own process group, wall-clock timeout, output cap, abort signal. */
const DEFAULT_TIMEOUT_MS = 120_000
const DEFAULT_MAX_OUTPUT_BYTES = 8 * 1024 * 1024
const KILL_GRACE_MS = 5_000

export type ProcessOptions = {
  timeoutMs?: number
  signal?: AbortSignal
  maxOutputBytes?: number
}

export type ProcessResult = {
  exit: number
  stdout: string
  stderr: string
  timedOut: boolean
  aborted: boolean
  outputLimitExceeded: boolean
}

function positiveInteger(value: string | undefined, fallback: number) {
  if (!value) return fallback
  const parsed = Number.parseInt(value, 10)
  return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback
}

export function subprocessMaxOutputBytes() {
  return positiveInteger(process.env.OPENCODE_SUBPROCESS_MAX_OUTPUT_BYTES, DEFAULT_MAX_OUTPUT_BYTES)
}

function defaultTimeoutMs() {
  return positiveInteger(process.env.OPENCODE_SUBPROCESS_TIMEOUT_MS, DEFAULT_TIMEOUT_MS)
}

function killProcessGroup(proc: Bun.Subprocess<"ignore", "pipe", "pipe">, signal: NodeJS.Signals) {
  try {
    if (process.platform !== "win32") {
      process.kill(-proc.pid, signal)
      return
    }
  } catch {}

  try {
    proc.kill(signal)
  } catch {}
}

async function readBounded(
  stream: ReadableStream<Uint8Array>,
  state: { captured: number; exceeded: boolean },
  maxOutputBytes: number,
  onLimit: () => void,
) {
  const reader = stream.getReader()
  const chunks: Buffer[] = []
  try {
    while (true) {
      const { value, done } = await reader.read()
      if (done) break
      const chunk = Buffer.from(value)
      const remaining = Math.max(0, maxOutputBytes - state.captured)
      if (remaining > 0) {
        const kept = chunk.subarray(0, remaining)
        chunks.push(kept)
        state.captured += kept.byteLength
      }
      if (chunk.byteLength > remaining && !state.exceeded) {
        state.exceeded = true
        onLimit()
      }
    }
  } finally {
    reader.releaseLock()
  }
  return Buffer.concat(chunks).toString("utf8")
}

/**
 * Prefix that starts `args` as the leader of a new process group, so a timeout can kill the whole tree
 * (`lake` spawns `lean`). Linux has `setsid`; macOS has none, so use perl's `setpgrp` there.
 */
function processGroupPrefix(): string[] {
  if (process.platform === "win32") return []
  if (which("setsid")) return ["setsid"]
  return ["perl", "-e", "setpgrp(0, 0); exec @ARGV or die $!", "--"]
}

/** Run a bounded subprocess in its own process group. */
export async function runProcess(args: string[], cwd: string, options: ProcessOptions = {}): Promise<ProcessResult> {
  const runArgs = [...processGroupPrefix(), ...args]
  const proc = Bun.spawn(runArgs, { stdout: "pipe", stderr: "pipe", cwd })
  const timeoutMs = options.timeoutMs ?? defaultTimeoutMs()
  const maxOutputBytes = options.maxOutputBytes ?? subprocessMaxOutputBytes()
  const capture = { captured: 0, exceeded: false }
  let timedOut = false
  let aborted = false
  let terminating = false
  let killTimer: Timer | undefined

  const terminate = () => {
    if (terminating) return
    terminating = true
    killProcessGroup(proc, "SIGTERM")
    killTimer = setTimeout(() => killProcessGroup(proc, "SIGKILL"), KILL_GRACE_MS)
    killTimer.unref?.()
  }
  const abortHandler = () => {
    aborted = true
    terminate()
  }
  if (options.signal?.aborted) abortHandler()
  else options.signal?.addEventListener("abort", abortHandler, { once: true })

  const timeoutTimer = setTimeout(() => {
    timedOut = true
    terminate()
  }, timeoutMs)
  timeoutTimer.unref?.()

  try {
    const [exit, stdout, stderr] = await Promise.all([
      proc.exited,
      readBounded(proc.stdout, capture, maxOutputBytes, terminate),
      readBounded(proc.stderr, capture, maxOutputBytes, terminate),
    ])
    return {
      exit,
      stdout,
      stderr,
      timedOut,
      aborted,
      outputLimitExceeded: capture.exceeded,
    }
  } finally {
    clearTimeout(timeoutTimer)
    if (killTimer) clearTimeout(killTimer)
    options.signal?.removeEventListener("abort", abortHandler)
  }
}
