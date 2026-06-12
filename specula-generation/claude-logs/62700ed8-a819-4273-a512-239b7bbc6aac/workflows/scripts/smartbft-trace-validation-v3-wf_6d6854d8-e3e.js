
export const meta = {
  name: 'smartbft-trace-validation-v3',
  description: 'Re-validate SmartBFT traces after TraceEnterNewView direct-state-update fix',
  phases: [
    { title: 'Validate', detail: 'run TLC on all 4 traces with updated Trace.tla' },
    { title: 'Diagnose', detail: 'for any remaining failures, extract exact blocked state and action' },
    { title: 'Report', detail: 'final summary' },
  ],
}

const SPECULA = '/Users/tess/dev/Specula/case-studies/smartbft/.specula-output'

phase('Validate')

const traces = [
  { name: 'trace_normal',      file: `${SPECULA}/traces/trace_normal.ndjson`,      lines: 31 },
  { name: 'trace_view_change', file: `${SPECULA}/traces/trace_view_change.ndjson`, lines: 49 },
  { name: 'trace_hb_timeout',  file: `${SPECULA}/traces/trace_hb_timeout.ndjson`,  lines: 64 },
  { name: 'trace_vc_deliver',  file: `${SPECULA}/traces/trace_vc_deliver.ndjson`,  lines: 40 },
]

const results = await parallel(traces.map(t => () =>
  agent(
    `Run TLC trace validation for SmartBFT. You MUST run TLC fresh — do not use cached results.

Trace: ${t.file}  (${t.lines} events)

spec_file:   "${SPECULA}/spec/Trace.tla"
config_file: "${SPECULA}/spec/Trace.cfg"
trace_file:  "${t.file}"
work_dir:    "${SPECULA}/spec/"

Key recent changes to Trace.tla:
- TraceEnterNewView now uses a DIRECT STATE-UPDATE formulation that checks m.view = Logline.view
  (not vc_view[s]+1). This allows enter_new_view events to fire even after SilentHandleViewChange
  advanced vc_view for followers.
- TraceHBFollowerTickAbsorb: absorbs hb_timeout when hbm_timed_out already TRUE
- SilentHBFollowerTickBeforeVC + SilentOnHeartbeatTimeout: fire before view_change_start
- SilentHandleViewChange + SilentProcessViewDataSameSeq: fire before enter_new_view

Use mcp__tracedebugger__run_trace_validation. If BFS times out, retry with simulation mode.

If the trace FAILS:
1. Report which trace event deadlocked (event name, 1-based index)
2. Report the EXACT precondition that blocked:
   - Which spec action was attempted (TraceXxx or SilentXxx)
   - Which guard/conjunct was NOT satisfied (e.g., "phase[3] = VC_STARTED but required NORMAL")
3. Dump the TLC state at the deadlock: all variable values that are relevant

Return JSON:
{
  "trace_name": "${t.name}",
  "passed": bool,
  "events_consumed": int,
  "error_type": "none"|"deadlock"|"invariant_violation"|"timeout"|"spec_error",
  "error_detail": string,   // if fail: which action blocked and which guard
  "failed_at_event": string,
  "failed_at_index": int,   // -1 if passed
  "total_events": ${t.lines}
}`,
    {
      label: `v3-${t.name}`,
      phase: 'Validate',
      schema: {
        type: 'object',
        properties: {
          trace_name:      { type: 'string' },
          passed:          { type: 'boolean' },
          events_consumed: { type: 'number' },
          error_type:      { type: 'string', enum: ['none','deadlock','invariant_violation','timeout','spec_error'] },
          error_detail:    { type: 'string' },
          failed_at_event: { type: 'string' },
          failed_at_index: { type: 'number' },
          total_events:    { type: 'number' },
        },
        required: ['trace_name','passed','events_consumed','error_type','error_detail','failed_at_event','failed_at_index','total_events'],
      },
    }
  )
))

const good = results.filter(Boolean).filter(r => r.passed)
const bad  = results.filter(Boolean).filter(r => !r.passed)
log(`Validation: ${good.length}/${traces.length} passed`)
for (const f of bad) {
  log(`FAIL ${f.trace_name}: ${f.error_type} at index ${f.failed_at_index} ("${f.failed_at_event}") — ${f.error_detail.slice(0,150)}`)
}

phase('Diagnose')

// For any still-failing traces, get deeper analysis
const deepDiags = bad.length > 0 ? await parallel(bad.map(r => () =>
  agent(
    `Deep-diagnose a trace validation failure for SmartBFT.

Trace: ${r.trace_name}, deadlock at event index ${r.failed_at_index} ("${r.failed_at_event}")
Error: ${r.error_detail}

Read the trace file at ${SPECULA}/traces/${r.trace_name}.ndjson to get events around index ${r.failed_at_index} (events ${Math.max(1, r.failed_at_index-3)} to ${r.failed_at_index+2}).

Read the spec at ${SPECULA}/spec/Trace.tla and find the action that handles "${r.failed_at_event}" events.

Determine:
1. What exact precondition in the spec action fails? (Check the base spec action's guards: phase, vc_view, msgs, etc.)
2. What state would be needed for the action to succeed?
3. Is this a spec issue (wrong guard), a silent-action issue (missing setup step), or an instrumentation issue (wrong trigger point)?
4. Propose a concrete fix (new silent action, guard relaxation, or direct-update formulation)

Keep answer under 200 words, be specific about variable names and values.`,
    { label: `diag-${r.trace_name}`, phase: 'Diagnose' }
  )
)) : []

phase('Report')

const summary = await agent(
  `Summarize SmartBFT trace validation after all recent Trace.tla fixes.

Pass/fail:
${results.filter(Boolean).map(r =>
  `${r.trace_name}: ${r.passed ? 'PASSED ('+r.events_consumed+'/'+r.total_events+' events)' : 
   'FAILED at event '+r.failed_at_index+' ('+r.failed_at_event+') — '+r.error_detail.slice(0,200)}`
).join('\n')}

Deep diagnoses (if any):
${deepDiags.filter(Boolean).map((d,i) => `${bad[i]?.trace_name}: ${typeof d === 'string' ? d.slice(0,300) : JSON.stringify(d).slice(0,300)}`).join('\n') || 'none'}

Write:
1. Overall status (N/4 pass)
2. What each passing trace validates
3. For any failures: root cause and exact fix needed
4. Is harness generation complete or blocked?

Under 250 words.`,
  { label: 'report-v3', phase: 'Report' }
)

return { results: results.filter(Boolean), summary }
