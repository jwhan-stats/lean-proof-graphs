# Input data

Place the rollout corpus at:

```text
data/k3-fsmzb-correct.jsonl
```

The expected file is the original `rollouts/lean/k3-fsmzb-correct.jsonl`
JSONL corpus. It is about 515 MB and is intentionally excluded from Git. The
checked 20- and 100-graph artifacts are included under `outputs/`, so validating
the published certificates does not require the corpus. Regenerating cohort
selection or graph extraction does require it.
