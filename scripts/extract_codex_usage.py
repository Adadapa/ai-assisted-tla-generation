import json
from datetime import datetime
from dateutil import parser

path = "../specula-generation/specula-output-codex/codex-session-019eb68f-6609-7da3-bbe5-bb38981fb613.jsonl"
# this script was generated with GPT 5.5
timestamps = []
last_total_usage = None
active_duration_ms = 0

with open(path, "r", encoding="utf-8") as f:
    for line in f:
        obj = json.loads(line)

        if "timestamp" in obj:
            timestamps.append(parser.isoparse(obj["timestamp"]))

        payload = obj.get("payload", {})

        if payload.get("type") == "token_count":
            last_total_usage = payload["info"]["total_token_usage"]

        if payload.get("type") in ["task_complete", "turn_aborted"]:
            if "duration_ms" in payload:
                active_duration_ms += payload["duration_ms"]

start = min(timestamps)
end = max(timestamps)

print("Transcript start:", start)
print("Transcript end:", end)
print("Transcript duration:", end - start)

print("Active task duration minutes:", active_duration_ms / 1000 / 60)

print("Final cumulative token usage:")
print(last_total_usage)

if last_total_usage:
    non_cached = (
        last_total_usage["input_tokens"]
        - last_total_usage["cached_input_tokens"]
    )
    print("Non-cached input tokens:", non_cached)