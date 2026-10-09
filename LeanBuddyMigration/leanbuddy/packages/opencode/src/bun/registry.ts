import { semver } from "bun"
import { text } from "node:stream/consumers"
import { Log } from "../util/log"
import { Process } from "../util/process"

export namespace PackageRegistry {
  const log = Log.create({ service: "bun" })

  function which() {
    return process.execPath
  }

  const INFO_TTL_MS = 10 * 60 * 1000
  const infoCache = new Map<string, { at: number; value: Promise<string | null> }>()

  /** `bun info`, shared by concurrent callers and remembered for INFO_TTL_MS: every project instance asks for the
   * same package version, and a burst of instances otherwise starts one registry query (≈200 MB each) apiece. */
  export async function info(pkg: string, field: string, cwd?: string): Promise<string | null> {
    const k = `${pkg}\u0000${field}`
    const hit = infoCache.get(k)
    if (hit && Date.now() - hit.at < INFO_TTL_MS) return hit.value
    const value = query(pkg, field, cwd)
    infoCache.set(k, { at: Date.now(), value })
    value.then((v) => v === null && infoCache.delete(k)).catch(() => infoCache.delete(k))
    return value
  }

  async function query(pkg: string, field: string, cwd?: string): Promise<string | null> {
    const result = Process.spawn([which(), "info", pkg, field], {
      cwd,
      stdout: "pipe",
      stderr: "pipe",
      env: {
        ...process.env,
        BUN_BE_BUN: "1",
      },
    })

    const code = await result.exited
    const stdout = result.stdout ? await text(result.stdout) : ""
    const stderr = result.stderr ? await text(result.stderr) : ""

    if (code !== 0) {
      log.warn("bun info failed", { pkg, field, code, stderr })
      return null
    }

    const value = stdout.trim()
    if (!value) return null
    return value
  }

  export async function isOutdated(pkg: string, cachedVersion: string, cwd?: string): Promise<boolean> {
    const latestVersion = await info(pkg, "version", cwd)
    if (!latestVersion) {
      log.warn("Failed to resolve latest version, using cached", { pkg, cachedVersion })
      return false
    }

    const isRange = /[\s^~*xX<>|=]/.test(cachedVersion)
    if (isRange) return !semver.satisfies(latestVersion, cachedVersion)

    return semver.order(cachedVersion, latestVersion) === -1
  }
}
