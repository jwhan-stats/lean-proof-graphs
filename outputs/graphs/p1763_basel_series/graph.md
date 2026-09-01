# basel_series

- Problem index: `1763`
- arXiv source: `math_0506415`
- Selected nodes / hyperedges: **2 / 2**
- Selected depth: **2**
- Retrieval events matched: **2 / 4**
- Incomplete target InfoTree snapshots audited/excluded: **0**
- Validation: original proof re-elaborated; every edge witness kernel-checked in its Lean local context; selected topology compiled as a separate Lean theorem.
- Axioms: `Classical.choice, Quot.sound, propext`
- Concrete certificate: [semantic_graph_certificate.lean](semantic_graph_certificate.lean) embeds the accepted proof and checks every selected raw witness, premise list, and conclusion against this graph.

![dependency graph](graph.svg)

## Hyperedges

| Edge | Premises | Conclusion | Rule | Retrieval |
|---|---|---|---|---|
| `h_001_h` | ∅ | h | `hasSum_nat_add_iff + hasSum_zeta_two` | loogle:1, leanfinder:2 |
| `h_goal` | h | goal | `simpa` | — |
