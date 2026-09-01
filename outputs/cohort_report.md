# Structured Lean dependency-graph cohort

This cohort contains **20** successful rollouts. Selection strategy: `shortest_sound_structured_stratified_by_helpers`; seed: `none`.

## What is checked

1. **Rollout gate:** the recorded `verify_submission` passed and placeholder tokens/warnings are absent.
2. **Semantic proof evidence:** the reconstructed theorem and accepted helper declarations elaborate under pinned Lean/Mathlib 4.29.0.
3. **Edge witnesses:** Lean's kernel type-checks every emitted proof value in its exact original local context, and its type is definitionally equal to the rendered conclusion. Transient target InfoTree bindings containing metavariables are audited and excluded, never promoted to edges.
4. **Projection link:** a SHA-256 dependency record ties the rendered premises and conclusion to the raw Lean evidence.
5. **Graph composition:** a generated `topology_certificate.lean` theorem composes precisely the selected hyperedges from boundary facts to the goal in a fresh Lean process.
6. **Concrete replay:** all 20 graph(s) include a self-contained `semantic_graph_certificate.lean`. Lean replays the accepted theorem value, kernel-checks each selected raw witness, and compares its ordered proposition premises and conclusion with the embedded graph manifest. The reviewed p1662 certificate additionally names one theorem per selected graph edge and composes only those theorems into the final result.
7. **Axiom audit:** transitive axioms are recorded; `sorryAx`-like dependencies fail validation.

The result is sound for the selected proof and projection policy. It is not a claim of uniqueness, task-level premise necessity, or globally minimum depth.

## Cohort summary

| Measure | Min | Median | Max |
|---|---:|---:|---:|
| Selected depth | 1 | 1 | 6 |
| Selected hyperedges | 1 | 1 | 10 |
| Maximum fan-in | 0 | 3 | 7 |
| Excluded incomplete InfoTree snapshots | 0 | 0 | 0 |

## Distributions

### Selected Depth

| Value | Graphs |
|---:|---:|
| `1` | 14 |
| `2` | 3 |
| `4` | 2 |
| `6` | 1 |

### Selected Hyperedge Count

| Value | Graphs |
|---:|---:|
| `1` | 14 |
| `2` | 3 |
| `5` | 2 |
| `10` | 1 |

### Max Fan In All

| Value | Graphs |
|---:|---:|
| `0` | 5 |
| `1` | 2 |
| `2` | 2 |
| `3` | 5 |
| `4` | 2 |
| `5` | 2 |
| `6` | 1 |
| `7` | 1 |

### Excluded Info Tree Binding Count

| Value | Graphs |
|---:|---:|
| `0` | 20 |

### Axiom Status

| Value | Graphs |
|---:|---:|
| `passed` | 20 |

## Gallery

| Graph | Depth | Edges | Fan-in |
|---|---:|---:|---:|
| [antitone_monotone_power_sum_inequality](graphs/p0960_antitone_monotone_power_sum_inequality/graph.md) | 6 | 10 | 5 |
| [intertwining_orbit_cocycle](graphs/p0818_intertwining_orbit_cocycle/graph.md) | 1 | 1 | 7 |
| [linfty_eq_erosion_distance](graphs/p0390_linfty_eq_erosion_distance/graph.md) | 1 | 1 | 0 |
| [two_minimal_missing_faces_deletion](graphs/p0381_two_minimal_missing_faces_deletion/graph.md) | 1 | 1 | 3 |
| [slope_composition_equivalent](graphs/p1489_slope_composition_equivalent/graph.md) | 1 | 1 | 6 |
| [exists_coloring_increasing_pairs](graphs/p1925_exists_coloring_increasing_pairs/graph.md) | 1 | 1 | 0 |
| [basel_series](graphs/p1763_basel_series/graph.md) | 2 | 2 | 1 |

## Recommended analysis unit

Use one row per graph for corpus-level summaries, one row per selected hyperedge for rule/retrieval analysis, and keep rejected attempts in a separate rollout table. Do not mix temporal proof-state transitions with forward semantic hyperedges.
