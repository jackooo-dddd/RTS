import fs from "fs"
import path from "path"
import { Log } from "../util/log"
import { which } from "../util/which"
import { LeanProject } from "./lean-project"

/**
 * Client for the Pantograph REPL (pinned 0.3.19, commit 92d4818; BACKEND_DECISION.md).
 *
 * One REPL process per (Lake project, import list), shared by every session of that workspace; requests are
 * serialised. The REPL is started as `lake env <repl> <modules…>` so it loads the project's `.olean`s, prints
 * `ready.`, and answers one JSON line per command line `<command> <json>`.
 *
 * Errors are classified (BACKEND_DECISION *Implementation answers*):
 * - `PantographError` with kind `command`: the REPL answered `{"error", "desc"}` (bad request, elaboration error
 *   of an input, …) — a tool error, never a proof retry;
 * - kind `backend`: the process died, did not start, hit the wall-clock or memory limit — the process is
 *   restarted on the next request; free under DECISIONS D5.
 * A failed tactic is *not* an error: `goal.tactic` returns a reply without `goals` and with `messages`.
 */
export namespace Pantograph {
  const log = Log.create({ service: "pantograph" })

  export class PantographError extends Error {
    constructor(
      readonly kind: "command" | "backend",
      readonly code: string,
      message: string,
    ) {
      super(message)
    }
  }

  export type Expression = { pp?: string; sexp?: string; dependentMVars?: string[] }
  export type Variable = { name: string; userName: string; isInaccessible?: boolean; type?: Expression; value?: Expression }
  export type Goal = { name: string; userName?: string; fragment?: string; target: Expression; vars: Variable[] }
  export type Message = { severity: string; data: string; pos?: { line: number; column: number } }
  export type TacticResult = {
    nextStateId?: number
    goals?: Goal[]
    messages?: Message[]
    hasSorry?: boolean
    hasUnsafe?: boolean
  }

  export const DEFAULT_REQUEST_TIMEOUT_MS = 120_000
  export const DEFAULT_START_TIMEOUT_MS = 300_000
  export const DEFAULT_MEMORY_LIMIT_MB = 12_000

  function positive(raw: string | undefined, fallback: number) {
    const parsed = Number.parseInt(raw ?? "", 10)
    return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback
  }

  export function config() {
    return {
      repl: process.env.OPENCODE_PANTOGRAPH_REPL?.trim() || which("pantograph-repl") || "",
      requestTimeoutMs: positive(process.env.OPENCODE_PANTOGRAPH_TIMEOUT_MS, DEFAULT_REQUEST_TIMEOUT_MS),
      startTimeoutMs: positive(process.env.OPENCODE_PANTOGRAPH_START_TIMEOUT_MS, DEFAULT_START_TIMEOUT_MS),
      memoryLimitMb: positive(process.env.OPENCODE_PANTOGRAPH_MEMORY_MB, DEFAULT_MEMORY_LIMIT_MB),
    }
  }

  type Pending = { resolve: (value: any) => void; reject: (error: Error) => void; timer: Timer }

  export class Process {
    private proc: Bun.Subprocess<"pipe", "pipe", "pipe"> | undefined
    private buffer = ""
    private queue: Promise<unknown> = Promise.resolve()
    private pending: Pending | undefined
    private ready: Promise<void> | undefined
    private watchdog: Timer | undefined
    private dead: PantographError | undefined
    /** Incremented on every (re)start; goal-state ids from an older generation are invalid. */
    generation = 0

    constructor(
      readonly root: string,
      readonly modules: string[],
      readonly settings = config(),
    ) {}

    get key() {
      return Process.key(this.root, this.modules)
    }

    static key(root: string, modules: string[]) {
      return `${path.resolve(root)}\u0000${[...modules].sort().join(" ")}`
    }

    private start() {
      if (!this.settings.repl || !fs.existsSync(this.settings.repl)) {
        throw new PantographError("backend", "PANTOGRAPH_UNAVAILABLE", `Pantograph REPL not found (OPENCODE_PANTOGRAPH_REPL=${this.settings.repl || "unset"})`)
      }
      this.generation++
      this.dead = undefined
      this.buffer = ""
      const proc = Bun.spawn([LeanProject.lake(), "env", this.settings.repl, ...this.modules], {
        cwd: this.root,
        stdin: "pipe",
        stdout: "pipe",
        stderr: "pipe",
      })
      this.proc = proc
      let markReady!: () => void
      let failReady!: (error: Error) => void
      this.ready = new Promise<void>((resolve, reject) => {
        markReady = resolve
        failReady = reject
      })
      const startTimer = setTimeout(() => {
        failReady(new PantographError("backend", "PANTOGRAPH_START_TIMEOUT", `Pantograph did not start within ${this.settings.startTimeoutMs} ms`))
        this.kill("start timeout")
      }, this.settings.startTimeoutMs)
      let started = false
      ;(async () => {
        const decoder = new TextDecoder()
        const reader = proc.stdout.getReader()
        while (true) {
          const { value: chunk, done } = await reader.read()
          if (done) break
          this.buffer += decoder.decode(chunk, { stream: true })
          let nl: number
          while ((nl = this.buffer.indexOf("\n")) >= 0) {
            const line = this.buffer.slice(0, nl)
            this.buffer = this.buffer.slice(nl + 1)
            if (!started) {
              if (line.trim() === "ready.") {
                started = true
                clearTimeout(startTimer)
                markReady()
              }
              continue
            }
            this.deliver(line)
          }
        }
        clearTimeout(startTimer)
        const stderr = await new Response(proc.stderr).text().catch(() => "")
        const error = new PantographError("backend", "PANTOGRAPH_EXITED", `Pantograph exited: ${stderr.slice(-2000)}`)
        this.dead = error
        if (!started) failReady(error)
        this.pending?.reject(error)
        this.pending = undefined
      })()
      this.watchdog = setInterval(() => this.checkMemory(), 5_000)
      this.watchdog.unref?.()
    }

    private deliver(line: string) {
      const pending = this.pending
      if (!pending) {
        log.warn("unexpected pantograph output", { line: line.slice(0, 200) })
        return
      }
      this.pending = undefined
      clearTimeout(pending.timer)
      if (line.startsWith("Error:")) {
        pending.reject(new PantographError("command", "PANTOGRAPH_MALFORMED", line))
        return
      }
      try {
        const value = JSON.parse(line)
        if (value && typeof value === "object" && "error" in value && "desc" in value) {
          pending.reject(new PantographError("command", String(value.error), String(value.desc)))
          return
        }
        pending.resolve(value)
      } catch {
        pending.reject(new PantographError("backend", "PANTOGRAPH_BAD_REPLY", `unparseable reply: ${line.slice(0, 500)}`))
      }
    }

    private checkMemory() {
      const pid = this.proc?.pid
      if (!pid) return
      const rss = residentMb(pid)
      if (rss !== undefined && rss > this.settings.memoryLimitMb) {
        const error = new PantographError("backend", "PANTOGRAPH_MEMORY_LIMIT", `Pantograph used ${Math.round(rss)} MB (limit ${this.settings.memoryLimitMb} MB) and was restarted`)
        this.pending?.reject(error)
        this.pending = undefined
        this.kill("memory limit")
      }
    }

    kill(reason: string) {
      log.info("killing pantograph", { root: this.root, reason })
      if (this.watchdog) clearInterval(this.watchdog)
      this.watchdog = undefined
      const proc = this.proc
      this.proc = undefined
      this.ready = undefined
      if (!proc) return
      for (const child of childPids(proc.pid)) {
        try {
          process.kill(child, "SIGKILL")
        } catch {}
      }
      try {
        proc.kill("SIGKILL")
      } catch {}
    }

    /** Send one command; requests are serialised. `timeoutMs` is the wall-clock limit for this request. */
    request<T = any>(command: string, payload: Record<string, unknown>, timeoutMs = this.settings.requestTimeoutMs): Promise<T> {
      const run = async () => {
        if (!this.proc || this.dead) this.start()
        await this.ready
        const proc = this.proc!
        return new Promise<T>((resolve, reject) => {
          const timer = setTimeout(() => {
            this.pending = undefined
            reject(new PantographError("backend", "PANTOGRAPH_TIMEOUT", `${command} did not answer within ${timeoutMs} ms; Pantograph was restarted`))
            this.kill("request timeout")
          }, timeoutMs)
          this.pending = { resolve, reject, timer }
          proc.stdin.write(`${command} ${JSON.stringify(payload)}\n`)
          proc.stdin.flush()
        })
      }
      const next = this.queue.then(run, run)
      this.queue = next.catch(() => undefined)
      return next
    }

    close() {
      try {
        this.proc?.stdin.write("\n")
        this.proc?.stdin.flush()
      } catch {}
      setTimeout(() => this.kill("close"), 2_000).unref?.()
    }
  }

  const processes = new Map<string, Process>()

  /** The shared process for a project and import list (started lazily on the first request). */
  export function forProject(root: string, modules: string[]) {
    const key = Process.key(root, modules)
    let proc = processes.get(key)
    if (!proc) {
      // A different import list for the same project replaces the old process (header changed, K1).
      for (const [other, existing] of processes) {
        if (existing.root === path.resolve(root) || path.resolve(existing.root) === path.resolve(root)) {
          existing.close()
          processes.delete(other)
        }
      }
      proc = new Process(path.resolve(root), modules)
      processes.set(key, proc)
    }
    return proc
  }

  export function shutdownAll() {
    for (const proc of processes.values()) proc.close()
    processes.clear()
  }

  function childPids(pid: number): number[] {
    try {
      const out = Bun.spawnSync(["pgrep", "-P", String(pid)]).stdout.toString()
      const kids = out.split(/\s+/).filter(Boolean).map(Number)
      return kids.flatMap((kid) => [kid, ...childPids(kid)])
    } catch {
      return []
    }
  }

  /** Resident memory (MB) of `pid` and its descendants (the REPL runs under `lake env`). */
  function residentMb(pid: number) {
    const pids = [pid, ...childPids(pid)]
    try {
      if (process.platform === "linux") {
        let kb = 0
        for (const p of pids) {
          const status = fs.readFileSync(`/proc/${p}/status`, "utf8")
          const match = /VmRSS:\s+(\d+)\s+kB/.exec(status)
          if (match) kb += Number(match[1])
        }
        return kb / 1024
      }
      const out = Bun.spawnSync(["ps", "-o", "rss=", "-p", pids.join(",")]).stdout.toString()
      return out.split(/\s+/).filter(Boolean).reduce((sum, value) => sum + Number(value), 0) / 1024
    } catch {
      return undefined
    }
  }
}
