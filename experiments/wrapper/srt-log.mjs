#!/usr/bin/env node
/**
 * srt-log: the outer sandbox, with a record of what it stopped.
 *
 * Runs a command (an agent, a script, anything) under Anthropic's sandbox
 * runtime with the outer policy (srt-outer.json). The OS blocks every write,
 * read or connection the policy denies (that part is srt). This wrapper adds the
 * record: each denial is written as one JSON line, classified the way the
 * reversibility model classifies boundary crossings.
 *
 * Usage:
 *   SRT_LIB=<path to sandbox-runtime dist/index.js> \
 *   node srt-log.mjs [--settings srt-outer.json] [--log denials.jsonl] -- <command...>
 *
 * SRT_LIB defaults to the package name, for when @anthropic-ai/sandbox-runtime is
 * resolvable. The literal "PROJ" in the settings is replaced by the working
 * directory, as probe.sh does.
 *
 * Logging limits (upstream sandbox-runtime, open at 0.0.83):
 *   - #806/#696/#720: srt's macOS monitor keeps only the first violation in each
 *     chunk of `log stream` output, so a burst of denials can be logged as one.
 *     Every process that is denied is likely flagged, but not every attempt.
 *   - #833: initialize() returns before `log stream` is reading; we wait 1 s.
 *   - Linux: srt's passive seccomp observer (kernel >= 5.5) is started by the same
 *     flag; untested here.
 * Blocking is unaffected by any of these: they only affect the record.
 */
import { appendFileSync, readFileSync } from 'node:fs'
import { spawn } from 'node:child_process'
import { randomUUID } from 'node:crypto'
import path from 'node:path'

// The run-later names come from the settings' denyWrite patterns ("**/name"),
// which Lean generates from the policy (`finalsay srt-config`), so the list
// lives in one place. A write to one is irreversible in the model's terms.
function runLaterNames(settings) {
  return (settings.filesystem?.denyWrite ?? [])
    .filter((g) => g.startsWith('**/'))
    .map((g) => g.slice(3).toLowerCase())
}

// Denials that are not boundary crossings: system queries every sandboxed
// process makes (sysctl reads, disk-space info, service lookups). srt denies them
// too, but logging them would bury the crossings. Shown with --verbose.
const NOISE = /deny\(\d+\)\s+(sysctl-read|system-info|mach-lookup|iokit-open|user-preference-read)\b/

function parseArgs(argv) {
  const out = { settings: 'srt-outer.json', log: 'denials.jsonl', verbose: false, command: [] }
  const dash = argv.indexOf('--')
  const opts = dash === -1 ? argv : argv.slice(0, dash)
  out.command = dash === -1 ? [] : argv.slice(dash + 1)
  for (let i = 0; i < opts.length; i++) {
    if (opts[i] === '--settings') out.settings = opts[++i]
    else if (opts[i] === '--log') out.log = opts[++i]
    else if (opts[i] === '--verbose') out.verbose = true
    else throw new Error(`unknown option ${opts[i]}`)
  }
  if (out.command.length === 0) throw new Error('nothing to run: put the command after --')
  return out
}

function shellQuote(s) {
  return /^[A-Za-z0-9_./=:@%+-]+$/.test(s) ? s : `'${s.replace(/'/g, `'\\''`)}'`
}

function loadSettings(file, project) {
  const text = readFileSync(file, 'utf8').replaceAll('"PROJ"', JSON.stringify(project))
  return JSON.parse(text)
}

/** Classify one violation line as a boundary crossing, naming the rule that stopped it. */
export function classify(line, project, runLater) {
  const op = (line.match(/\b(file-write[\w-]*|file-read[\w-]*|network[\w-]*|process-exec[\w-]*|mach-lookup)\b/) || [])[1] ?? 'unknown'
  const p = (line.match(/(\/[^\s"']+)/) || [])[1] ?? null
  let kind = 'other'
  let rule = null
  if (op.startsWith('file-write')) {
    const segs = p ? p.split('/').map((s) => s.toLowerCase()) : []
    const hit = runLater.find((n) => segs.includes(n))
    if (hit) { kind = 'run-later-write'; rule = `**/${hit}` }          // irreversible: runs outside later
    else if (p && !p.startsWith(project + path.sep) && p !== project) {
      kind = 'write-outside-project'; rule = 'allowWrite'              // outside the restorable boundary
    } else kind = 'write-denied'
  } else if (op.startsWith('file-read')) {
    kind = 'read-denied'; rule = 'denyRead'   // private data: a read that could feed a send
  } else if (op.startsWith('network') || /deny network|blocked-by-sandbox|connection not allowed/i.test(line)) {
    kind = 'network-egress'; rule = 'network' // information leaving the boundary
  }
  return { op, path: p, kind, rule }
}

async function main() {
  const args = parseArgs(process.argv.slice(2))
  const project = process.cwd()
  const { SandboxManager } = await import(process.env.SRT_LIB ?? '@anthropic-ai/sandbox-runtime')

  const settings = loadSettings(args.settings, project)
  const runLater = runLaterNames(settings)
  // Third argument: enable the macOS violation log monitor (off by default in srt).
  await SandboxManager.initialize(settings, undefined, true)
  // Give `log stream` a moment to attach before the command starts.
  // (One startup miss seen at 500 ms; 1 s leaves margin.)
  await new Promise((r) => setTimeout(r, 1000))
  const session = randomUUID()
  const commandText = args.command.map(shellQuote).join(' ')
  const wrapped = await SandboxManager.wrapWithSandbox(commandText, undefined, undefined, undefined, {
    commandId: session,
    commandText,
  })

  // The store hands every listener the whole (bounded) tail; log only what is new.
  const store = SandboxManager.getSandboxViolationStore()
  let logged = store.getTotalCount()
  let stopped = 0
  const unsubscribe = store.subscribe((tail) => {
    const total = store.getTotalCount()
    const fresh = tail.slice(Math.max(0, tail.length - (total - logged)))
    logged = total
    for (const v of fresh) {
      if (!args.verbose && NOISE.test(v.line)) continue
      stopped++
      const record = {
        ts: (v.timestamp instanceof Date ? v.timestamp : new Date()).toISOString(),
        event: 'stopped',
        session,
        command: v.command ?? commandText,
        ...classify(v.line, project, runLater),
        line: v.line,
      }
      appendFileSync(args.log, JSON.stringify(record) + '\n')
    }
  })

  const child = spawn(wrapped, { shell: true, stdio: 'inherit' })
  const code = await new Promise((resolve) => child.on('exit', (c, sig) => resolve(c ?? (sig ? 128 : 1))))

  // macOS delivers sandbox log lines asynchronously; give the tail a moment.
  await new Promise((r) => setTimeout(r, 750))
  unsubscribe()
  await SandboxManager.reset()
  if (stopped > 0) console.error(`srt-log: stopped ${stopped} action(s); see ${args.log}`)
  process.exit(code)
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch((err) => {
    console.error(`srt-log: ${err.message}`)
    process.exit(1)       // fail closed: if the sandbox can't start, nothing runs
  })
}
