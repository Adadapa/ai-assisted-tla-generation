
export const meta = {
  name: 'smartbft-trace-validation-v2',
  description: 'Re-validate SmartBFT traces after Trace.tla fixes (TraceHBFollowerTickAbsorb + SilentHandleViewChange + SilentProcessViewDataSameSeq)',
  phases: [
    { title: 'Validate', detail: 'run TLC trace validation on each trace file with updated Trace.tla' },
    { title: 'Report', detail: 'summarize pass/fail and diagnose any remaining deadlocks' },
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
    `Run TLA+ trace validation for SmartBFT. The Trace.tla spec was recently updated (new silent actions added). You MUST run TLC fresh — do not use any cached or prior results.

Trace file: ${t.file}  (${t.lines} events)

Use mcp__tracedebugger__run_trace_validation with:
  spec_file:   "${SPECULA}/spec/Trace.tla"
  config_file: "${SPECULA}/spec/Trace.cfg"
  trace_file:  "${t.file}"
  work_dir:    "${SPECULA}/spec/"

IMPORTANT: The Trace.tla now contains new actions: TraceHBFollowerTickAbsorb, SilentHandleViewChange, SilentProcessViewDataSameSeq. These were not present in previous runs.

If BFS times out (>300s), re-run with simulation mode: add flag -simulate (or additional_options "-simulate -depth 500 -seed 1") if the tool supports it.

After TLC finishes, return a JSON object:
{
  "trace_name": "${t.name}",
  "passed": <true if all events consumed and TraceMatched satisfied>,
  "events_consumed": <how many trace events advanced l>,
  "error_type": "none"|"deadlock"|"invariant_violation"|"timeout"|"spec_error",
  "error_detail": "<what went wrong, empty if passed>",
  "failed_at_event": "<event name at deadlock, empty if passed>",
  "failed_at_index": <1-based trace line index at deadlock, -1 if passed>,
  "total_events": ${t.lines}
}`,
    {
      label: `validate-v2-${t.name}`,
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
log(`Validation complete: ${good.length}/${traces.length} passed`)
for (const f of bad) {
  log(`FAIL ${f.trace_name}: ${f.error_type} at event ${f.failed_at_index} ("${f.failed_at_event}") — ${f.error_detail.slice(0,120)}`)
}

phase('Report')

const summary = await agent(
  `Summarize SmartBFT trace validation after Trace.tla was updated with:
  - TraceHBFollowerTickAbsorb: absorbs hb_timeout when hbm_timed_out already TRUE
  - SilentHBFollowerTickBeforeVC: fires HBFollowerTick before view_change_start if not yet timed out
  - SilentOnHeartbeatTimeout: fires OnHeartbeatTimeout before view_change_start
  - SilentHandleViewChange: fires HandleViewChange before enter_new_view / vc events
  - SilentProcessViewDataSameSeq: fires ProcessViewDataSameSeq before enter_new_view

Results:
${results.filter(Boolean).map(r =>
  `${r.trace_name}: ${r.passed ? 'PASSED' : 'FAILED'} (${r.events_consumed}/${r.total_events} events consumed)` +
  (r.passed ? '' : `\n  Error: ${r.error_type} at event ${r.failed_at_index} "${r.failed_at_event}"\n  Detail: ${r.error_detail.slice(0,400)}`)
).join('\n')}

Write a summary covering:
1. How many traces now pass
2. For any failures: exact diagnosis — is it still the same deadlock pattern? New problem? Which spec action is blocked and what precondition fails?
3. Next step recommendation

Under 250 words.`,
  { label: 'report-v2', phase: 'Report' }
)

return { results: results.filter(Boolean), summary }
