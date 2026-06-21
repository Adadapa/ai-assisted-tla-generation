#!/usr/bin/env python3
"""
Summarize SANY-like errors found in action_decomposition result directories.

Reads saved result.json files under output/action_decomposition/... and reports,
per timestamped run, which SANY error classes were found and how many times.

Examples:
  python3 scripts/summarize_action_decomp_sany.py
  python3 scripts/summarize_action_decomp_sany.py --task hyperledger
  python3 scripts/summarize_action_decomp_sany.py --model gemini
  python3 scripts/summarize_action_decomp_sany.py --details

This file was generated with gpt 5.5
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_ROOT = PROJECT_ROOT / "output" / "action_decomposition"
sys.path.insert(0, str(PROJECT_ROOT))

from tla_eval.core.verification.sany_error_code_reverse import classify_sany_error_message


def iter_result_files(root: Path) -> Iterable[Path]:
    yield from sorted(root.glob("**/result.json"))


def classify_error(msg: str) -> str:
    match = classify_sany_error_message(msg)
    if match:
        return match.error_name

    text = msg.lower()
    if "semantic errors:" in text:
        return "OTHER_SANY_ERROR"
    if "syntax error" in text or "fatal errors while parsing" in text:
        return "GENERAL_PARSE_ERROR"
    return "UNCLASSIFIED"


def run_matches_filters(result_path: Path, task_filter: str | None, model_filter: str | None) -> bool:
    parts = result_path.parts
    try:
        i = parts.index("action_decomposition")
        task = parts[i + 2]
        model = parts[i + 3]
    except (ValueError, IndexError):
        return False

    if task_filter and task_filter not in task:
        return False
    if model_filter and model_filter not in model:
        return False
    return True


def summarize_run(result_path: Path) -> tuple[str, str, str, Counter, dict[str, list[str]]]:
    parts = result_path.parts
    i = parts.index("action_decomposition")
    task = parts[i + 2]
    model = parts[i + 3]
    timestamp = parts[i + 4]

    data = json.loads(result_path.read_text())
    counts: Counter = Counter()
    details: dict[str, list[str]] = defaultdict(list)

    for action_result in data.get("action_results", []):
        if action_result.get("success", True):
            continue
        action_name = action_result.get("action_name", "<unknown>")
        for err in action_result.get("syntax_errors", []):
            kind = classify_error(err)
            counts[kind] += 1
            details[kind].append(action_name)
        for err in action_result.get("semantic_errors", []):
            kind = classify_error(err)
            counts[kind] += 1
            details[kind].append(action_name)

    return task, model, timestamp, counts, details


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=str(DEFAULT_ROOT), help="Root directory to scan")
    ap.add_argument("--task", help="Substring filter on task directory, e.g. hyperledger")
    ap.add_argument("--model", help="Substring filter on model directory, e.g. gemini")
    ap.add_argument("--details", action="store_true", help="Also print failing actions per error type")
    args = ap.parse_args()

    root = Path(args.root)
    if not root.exists():
        print(f"Root not found: {root}")
        return 1

    found = False
    for result_path in iter_result_files(root):
        if not run_matches_filters(result_path, args.task, args.model):
            continue
        task, model, timestamp, counts, details = summarize_run(result_path)
        found = True

        print(f"{timestamp}  task={task}  model={model}")
        if not counts:
            print("  no SANY failures recorded")
            continue

        for error_name, n in counts.most_common():
            print(f"  {error_name}: {n}")
            if args.details:
                actions = ", ".join(details[error_name])
                print(f"    actions: {actions}")

    if not found:
        print("No matching result.json files found.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
