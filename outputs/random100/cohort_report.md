# Structured Lean dependency-graph cohort

This cohort contains **100** successful rollouts. Selection strategy: `deterministic_hash_sample`; seed: `arxivlean-dependency-graph-random100-v1`.

## What is checked

1. **Rollout gate:** the recorded `verify_submission` passed and placeholder tokens/warnings are absent.
2. **Semantic proof evidence:** the reconstructed theorem and accepted helper declarations elaborate under pinned Lean/Mathlib 4.29.0.
3. **Edge witnesses:** Lean's kernel type-checks every emitted proof value in its exact original local context, and its type is definitionally equal to the rendered conclusion. Transient target InfoTree bindings containing metavariables are audited and excluded, never promoted to edges.
4. **Projection link:** a SHA-256 dependency record ties the rendered premises and conclusion to the raw Lean evidence.
5. **Graph composition:** a generated `topology_certificate.lean` theorem composes precisely the selected hyperedges from boundary facts to the goal in a fresh Lean process.
6. **Concrete replay:** all 100 graph(s) include a self-contained `semantic_graph_certificate.lean`. Lean replays the accepted theorem value, kernel-checks each selected raw witness, and compares its ordered proposition premises and conclusion with the embedded graph manifest. The reviewed p1662 certificate additionally names one theorem per selected graph edge and composes only those theorems into the final result.
7. **Axiom audit:** transitive axioms are recorded; `sorryAx`-like dependencies fail validation.

The result is sound for the selected proof and projection policy. It is not a claim of uniqueness, task-level premise necessity, or globally minimum depth.

## Cohort summary

| Measure | Min | Median | Max |
|---|---:|---:|---:|
| Selected depth | 1 | 1 | 8 |
| Selected hyperedges | 1 | 1 | 22 |
| Maximum fan-in | 0 | 3.5 | 20 |
| Excluded incomplete InfoTree snapshots | 0 | 0 | 17 |

## Distributions

### Selected Depth

| Value | Graphs |
|---:|---:|
| `1` | 60 |
| `2` | 16 |
| `3` | 3 |
| `4` | 11 |
| `5` | 4 |
| `6` | 3 |
| `7` | 2 |
| `8` | 1 |

### Selected Hyperedge Count

| Value | Graphs |
|---:|---:|
| `1` | 60 |
| `2` | 12 |
| `3` | 3 |
| `4` | 4 |
| `5` | 2 |
| `6` | 4 |
| `7` | 1 |
| `8` | 5 |
| `10` | 4 |
| `11` | 1 |
| `14` | 2 |
| `16` | 1 |
| `22` | 1 |

### Max Fan In All

| Value | Graphs |
|---:|---:|
| `0` | 10 |
| `1` | 10 |
| `2` | 11 |
| `3` | 19 |
| `4` | 17 |
| `5` | 9 |
| `6` | 13 |
| `7` | 4 |
| `8` | 1 |
| `9` | 3 |
| `10` | 2 |
| `20` | 1 |

### Excluded Info Tree Binding Count

| Value | Graphs |
|---:|---:|
| `0` | 97 |
| `2` | 1 |
| `16` | 1 |
| `17` | 1 |

### Axiom Status

| Value | Graphs |
|---:|---:|
| `passed` | 100 |

## Gallery

| Graph | Depth | Edges | Fan-in |
|---|---:|---:|---:|
| [laurent_circulant_kernel](graphs/p3019_laurent_circulant_kernel/graph.md) | 8 | 10 | 4 |
| [binary_quadratic_form_volume_identity](graphs/p1662_binary_quadratic_form_volume_identity/graph.md) | 6 | 22 | 6 |
| [connected_nodal_domain_of_leading_eigenvector](graphs/p3112_connected_nodal_domain_of_leading_eigenvec/graph.md) | 5 | 8 | 20 |
| [catlin_vertical_curve_is_geodesic](graphs/p0912_catlin_vertical_curve_is_geodesic/graph.md) | 4 | 8 | 6 |
| [graded_dual_rational_map_mem_completion](graphs/p2674_graded_dual_rational_map_mem_completion/graph.md) | 3 | 4 | 3 |
| [independentDominationNumber_eq_dominationNumber](graphs/p0043_independentdominationnumber_eq_dominationn/graph.md) | 1 | 1 | 1 |
| [continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization](graphs/p1226_continuous_quadratic_form_delta_semidefini/graph.md) | 1 | 1 | 3 |
| [pendant_branch_laplacian_eigenvector_decay](graphs/p2116_pendant_branch_laplacian_eigenvector_decay/graph.md) | 1 | 1 | 6 |
| [horseshoeLikePenalty_strictConcave](graphs/p3255_horseshoelikepenalty_strictconcave/graph.md) | 1 | 1 | 1 |
| [diagonal_homogeneous_polynomial_norm_bounds](graphs/p1232_diagonal_homogeneous_polynomial_norm_bound/graph.md) | 4 | 5 | 7 |

## Recommended analysis unit

Use one row per graph for corpus-level summaries, one row per selected hyperedge for rule/retrieval analysis, and keep rejected attempts in a separate rollout table. Do not mix temporal proof-state transitions with forward semantic hyperedges.
