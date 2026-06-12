
export const meta = {
  name: 'smartbft-trace-validation',
  description: 'Validate all 4 SmartBFT traces against the fixed Trace.tla spec',
  phases: [
    { title: 'Validate', detail: 'run TLC trace validation on each trace file' },
    { title: 'Report', detail: 'summarize pass/fail and remaining issues' },
  ],
}

const SPECULA = '/Users/tess/dev/Specula/case-studies/smartbft/.specula-output'

phase('Validate')

const traces = [
  { name: 'trace_normal',      file: `${SPECULA}/traces/trace_normal.ndjson` },
  { name: 'trace_view_change', file: `${SPECULA}/traces/trace_view_change.ndjson` },
  { name: 'trace_hb_timeout',  file: `${SPECULA}/traces/trace_hb_timeout.ndjson` },
  { name: 'trace_vc_deliver',  file: `${SPECULA}/traces/trace_vc_deliver.ndjson` },
]

const results = await parallel(traces.map(t => () =>
  agent(
    `Run TLA+ trace validation for SmartBFT trace file: ${t.file}

Use the mcp__tracedebugger__run_trace_validation tool with these exact parameters:
- spec_file: "${SPECULA}/spec/Trace.tla"
- config_file: "${SPECULA}/spec/Trace.cfg"
- trace_file: "${t.file}"
- work_dir: "${SPECULA}/spec/"

If TLC times out in BFS mode (state space explosion), retry with simulation mode by passing additional_options: "-simulate -depth 500 -seed 1" to run_trace_validation (check if the tool supports this parameter; if not, re-run with "-simulate" flag if available, otherwise report the timeout as a separate finding).

Report:
- passed: did validation succeed (all events consumed, TraceMatched satisfied)?
- events_consumed: how many trace events were processed before success/failure
- error_type: "none" | "deadlock" | "invariant_violation" | "timeout" | "spec_error"
- error_detail: what went wrong (empty if passed)
- failed_at_event: which event name caused deadlock (if applicable)
- failed_at_index: which trace line index (1-based, if applicable)
- total_events: total number of events in the trace file

Return a JSON object with those fields plus trace_name: "${t.name}".`,
    {
      label: `validate-${t.name}`,
      phase: 'Validate',
      schema: {
        type: 'object',
        properties: {
          trace_name: { type: 'string' },
          passed: { type: 'boolean' },
          events_consumed: { type: 'number' },
          error_type: { type: 'string', enum: ['none', 'deadlock', 'invariant_violation', 'timeout', 'spec_error'] },
          error_detail: { type: 'string' },
          failed_at_event: { type: 'string' },
          failed_at_index: { type: 'number' },
          total_events: { type: 'number' },
        },
        required: ['trace_name', 'passed', 'events_consumed', 'error_type', 'error_detail', 'failed_at_event', 'failed_at_index', 'total_events'],
      },
    }
  )
))

const good = results.filter(Boolean).filter(r => r.passed)
const bad = results.filter(Boolean).filter(r => !r.passed)

log(`Validation complete: ${good.length}/${traces.length} passed`)
for (const f of bad) {
  log(`FAIL ${f.trace_name}: ${f.error_type} at event ${f.failed_at_index} (${f.failed_at_event}) — ${f.error_detail.slice(0, 100)}`)
}

phase('Report')

const summary = await agent(
  `Summarize SmartBFT trace validation results.

Results:
${results.filter(Boolean).map(r =>
  `${r.trace_name}: ${r.passed ? 'PASSED' : 'FAILED'} (${r.events_consumed}/${r.total_events} events consumed)` +
  (r.passed ? '' : `\n  Error: ${r.error_type} at event ${r.failed_at_index} "${r.failed_at_event}"\n  Detail: ${r.error_detail.slice(0, 300)}`)
).join('\n')}

The Trace.tla spec was recently fixed by adding two new silent actions:
1. SilentHBFollowerTickBeforeVC — fires HBFollowerTick(s) when ~hbm_timed_out[s] before view_change_start
2. SilentOnHeartbeatTimeout — fires OnHeartbeatTimeout(s) when phase[s]="NORMAL" before view_change_start

These fix a gap where view_change_start can fire before the node's own hb_timeout in concurrent execution.

Write a summary covering:
1. Overall status (all pass / partial pass / all fail)
2. For each passing trace: what the trace covers
3. For any remaining failures: exact diagnosis and whether it is a spec issue vs instrumentation issue
4. Recommendation for next step (proceed to validation-workflow / fix remaining issues)

Keep it under 300 words.`,
  { label: 'summary', phase: 'Report' }
)

return {
  results: results.filter(Boolean),
  summary,
}
