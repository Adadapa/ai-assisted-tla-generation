# ai-assisted-tla-generation
Research project to asses generation of TLA+ specifications using AI-assisted approaches. This repo contains all the results and the reproduction package.

## Directory Overview

### Generated Specifications

- `generated_specs/` stores AI-generated TLA+ specifications and model-checking artifacts produced by different generation approaches.
- `generated_specs/codex/` contains the Codex-generated SmartBFT specification together with its base and model-checker configuration files presented by Specula.
- `generated_specs/deepseek/` contains DeepSeek-generated base, trace, and model-checking specification files for SmartBFT.
- `generated_specs/deepseek/combined/` contains DeepSeek outputs where the multiple specifications generated with Specula are flattened into one spec to be fed into SysMoBench.
- `generated_specs/direct_prompting/` stores timestamped direct-prompting runs and their outputs for Gemini models.
- `generated_specs/direct_prompting/gemini_25_flash/` contains Gemini 2.5 Flash direct-prompting runs.
- `generated_specs/direct_prompting/gemini_25_pro/` contains Gemini 2.5 Pro direct-prompting runs.

### Experiment Logs

- `logs/` stores execution, compilation, decomposition, and coverage logs grouped by model family. These are SysMoBench outputs.
- `logs/codex/` contains Codex run logs for invariant checking, runtime checks, and coverage-related experiments.
- `logs/deepseek/` contains DeepSeek compilation, runtime, and coverage logs for generated specifications.
- `logs/gemini_flash/` contains Gemini Flash logs for multiple compilation attempts.
- `logs/gemini_pro/` contains Gemini Pro logs for multiple compilation attempts.

### Specula Experiments

- `specula-generation/` stores Specula-related experiment notes, raw model logs, and generated output bundles.
- `specula-generation/claude-logs/` contains Claude session logs and per-run trace directories captured during Specula experiments.
- `specula-generation/specula-output-codex/` contains the Codex Specula output bundle, including reports, harness code, generated specs, traces, and Go caches.
- `specula-generation/specula-output-deepseek/` is reserved for DeepSeek Specula output bundles.

### SysMoBench

- `sysmobench-generation/` stores SysMoBench generation inputs, including task definitions, invariant sets, and prompt templates.
- `sysmobench-generation/prompts/` contains the prompt templates used across the SysMoBench generation phases.
- `sysmobench-evaluation/` stores SysMoBench evaluation outputs, including result summaries and run transcripts.
- `sysmobench-evaluation/results/` contains evaluation result files grouped by different metrics.
- `sysmobench-evaluation/transcripts/` contains captured evaluation transcripts such as trace-validation attempts.

### Scripts
- `scripts/extract_codex_usage.py` is the script used for extracting token usage out of codex sessions
- `scripts/promQL_query_for_token_usage` the PromQL query used on the Google Cloud Metrics Dashboard to extract the token usage of Gemini models
- `scripts/summarize_action_decomp.py` is the script used for gathering compilation error statistics out of SysMoBench results

## Remarks
For SysMoBench evaluation the run_benchmark commands below were used. Please refr to `sysmobench-generation/models_configuration.yaml` for configuring the LLM models used.
- python3 scripts/run_benchmark.py --task hyperledger --method direct_call --model [gemini25flash_google, gemini25_google] --metric [direct_call, action_decomposition, invariant_check, runtime_coverage]