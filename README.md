# Lean Proof Dependency Graphs

This repository turns successful Lean proving rollouts into checked dependency
hypergraphs. The original 20-item pilot is retained, and a fixed-seed 100-item
cohort avoids shortest-proof selection bias. The graph contract, sampling
rationale, visual grammar, and Lean guarantees are specified in
[`METHODOLOGY.md`](METHODOLOGY.md).

The generated 100-item cohort is at
[`outputs/random100/cohort_report.md`](outputs/random100/cohort_report.md); the
original pilot remains at [`outputs/index.md`](outputs/index.md). Each graph has
six core linked artifacts:

- `graph.svg`: presentation-friendly rendering
- `graph.dot`: Graphviz source
- `graph.json`: complete graph, provenance, retrieval overlay, metrics, and validation status
- `graph.md`: compact human-readable edge table
- `topology_certificate.lean`: generated Lean proof that the selected edges
  compose from boundary facts to the goal
- `semantic_graph_certificate.lean`: self-contained accepted proof plus a Lean
  command that checks its concrete selected witnesses against `graph.json`

The p1662 file uses an expanded reviewed format: it has one executable theorem
for every concrete graph edge and a final theorem composed only from those
edge theorems. Its generated type bridge applies every theorem at the exact
premises and conclusion rendered in `graph.json`.

## Pipeline

```text
rollout JSONL
  → pair tool calls with results
  → soundness and verification gate
  → declared deterministic cohort selection
  → reconstruct accepted helpers + final submission
  → Lean 4.29 / Mathlib 4.29 batch elaboration
  → kernel-checked local witnesses and direct proof-term dependencies
  → retrieval overlay
  → JSON + SVG + DOT + Markdown + axiom audit
  → fresh Lean topology-certificate compilation
  → self-contained concrete semantic replay for every graph
  → provenance, structure, rendering, and metric validation
```

`GraphExporter.lean` reads the final theorem value accepted by Lean. Proposition-valued theorem arguments become manifest nodes. Proposition-valued `let`/`have` binders become derived nodes. For each emitted derived binder, its proof term's **direct** free proposition variables are the joint premises of one hyperedge. Lean's kernel checks that proof value in its exact local context, and its inferred type must be definitionally equal to the rendered conclusion. If a transient target InfoTree snapshot still contains metavariables, it is recorded in `excluded_local_bindings` and is never emitted as an edge. Universal introduction stays at the graph boundary, and named Mathlib declarations are treated atomically. Accepted rollout helper theorems are also atomic, but are separately tagged as `rollout_helper_declaration` rather than being mislabeled as Mathlib.

Lean's internal `FVarId` is retained as binding identity. This matters when two binders print identically or when a tactic such as `dsimp ... at h` changes the displayed form of the same hypothesis.

Search calls are not reasoning nodes. A retrieved declaration is attached to a selected edge only when that declaration occurs in the edge's proof term. Unmatched searches remain in `retrieval_events` as rollout provenance.

## Validate the published artifacts

From this directory:

```bash
lake update
lake build graph_exporter
lake build graph_certificate
python3 scripts/pipeline.py validate --config configs/random100.json --output outputs/random100
python3 -m unittest discover -s tests -p 'test_*.py'
```

This recompiles the 100 abstract topology certificates and all 100 concrete
semantic certificates. The published proof and raw elaboration evidence are
included, so validation does not require the original rollout corpus.

## Regenerate from the rollout corpus

The approximately 515 MB source JSONL is not committed. Place it at
`data/k3-fsmzb-correct.jsonl` as described in
[`data/README.md`](data/README.md), then run:

```bash
python3 scripts/pipeline.py scan --config configs/random100.json --output outputs/random100
python3 scripts/pipeline.py all --config configs/random100.json --output outputs/random100
```

`lake-manifest.json`, `lean-toolchain`, and `lakefile.lean` pin Lean and Mathlib to 4.29.0. The exporter elaborates uncached candidates in isolated namespaces and bounded batches. Raw graphs are cached by schema, proof hash, Lean version, theorem name, and isolation mode; extending the sample therefore elaborates only newly selected proofs. A failing batch is bisected until the failing rollout is named. If namespace wrapping changes extension-style name resolution, that singleton is retried from its exact reconstructed source and the `standalone_source` mode is recorded. Individual reconstructed proofs remain under the cohort's `candidates/` directory for inspection.

To rebuild only the projections and renderings from existing raw Lean evidence:

```bash
python3 scripts/pipeline.py all --config configs/random100.json --output outputs/random100 --skip-lean
```

To deliberately ignore valid cache entries and repeat Lean extraction:

```bash
python3 scripts/pipeline.py all --config configs/random100.json --output outputs/random100 --force-lean
```

## Selection and soundness

The input expected at `data/k3-fsmzb-correct.jsonl` is the original
`rollouts/lean/k3-fsmzb-correct.jsonl` corpus. Selection is deterministic and
declared per config. `configs/random100.json` ranks every eligible rollout by a
seeded hash, so token length does not determine inclusion.
`configs/coverage48.json` instead balances source-level structure strata for
qualitative coverage. The original `config.json` keeps the shortest-20 policy
only as a smoke test. Every selected rollout has at least one `have`/`suffices`,
at least one retrieval event, and a successful `verify_submission` result.

The pipeline does **not** trust `metadata.correct` by itself. In this input, verified-looking records can still contain `sorry`, and the verifier may report that the declaration uses it. The gate therefore rejects:

- missing or failed `verify_submission` calls;
- verifier warnings reporting `sorry`, `admit`, `axiom`, or `sorryAx`;
- those tokens in accepted helper code or the final submission, after removing nested comments and strings.

The exact eligible population, stratum counts, seed, hash ranks, rejection counts, and selected IDs are stored in each cohort's `candidate_audit.json`.

## Graph semantics

- Node: one proposition-valued binder from the theorem-value telescope, with a target InfoTree fallback when the final proof term does not retain the intermediate binder.
- Hyperedge: all proposition binders directly referenced by one proof value, jointly implying that binder's proposition.
- Manifest: proposition-valued assumptions supplied at the theorem boundary.
- Goal: the theorem body after boundary introduction.
- Selected graph: the backward dependency closure of the goal; unused local facts remain available in JSON but are not rendered.
- Depth and fan-in: computed on direct dependencies, with side conditions retained and tagged.
- Retrieval usefulness: counted only on selected edges and only by observed declaration-name matches.

An empty-premise edge is a closed proof step, usually discharged by a Mathlib declaration or tactic-generated proof term.

## Validation boundary

`python3 scripts/pipeline.py validate` checks the configured cohort size, unique IDs, edge references, exact selected goal closure, acyclicity, absence of unresolved selected derived nodes, recomputed metrics, SVG XML, DOT wrappers, raw evidence versions, proof hashes, axiom audit, the audited InfoTree-exclusion ledger, and the placeholder gate on reconstructed source.

Every **emitted** local edge witness is kernel-checked in its original Lean context; incomplete editor snapshots are counted and excluded rather than treated as evidence. A dependency fingerprint connects the JSON edge to that raw witness, and the generated `topology_certificate.lean` independently proves that the selected closure composes to the goal.

Validation also recompiles every graph's `semantic_graph_certificate.lean` in
a fresh Lean process. The file contains the complete reconstructed proof;
[`GraphCertificate.lean`](GraphCertificate.lean) locates each selected raw
witness in the elaborated theorem value, kernel-checks it, and compares its
ordered proposition dependencies and conclusion with the embedded manifest.
The pipeline requires deterministic source plus matching topology, proof, and
certificate hashes. The expanded
[`p1662 certificate`](semantic_certificates/p1662_binary_quadratic_form_volume_identity.lean)
also checks an exact named theorem set, one theorem per selected edge.

This is a sound projection of the selected proof, not a complete editor trace
or a claim that the mathematical decomposition is unique or globally minimal.
See [`METHODOLOGY.md`](METHODOLOGY.md) for the exact claim boundary.

## License

The code and included artifacts are released under the
[MIT License](LICENSE).
