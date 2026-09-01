# intertwining_orbit_cocycle

- Problem index: `818`
- arXiv source: `math_0408120`
- Selected nodes / hyperedges: **8 / 1**
- Selected depth: **1**
- Retrieval events matched: **0 / 2**
- Incomplete target InfoTree snapshots audited/excluded: **0**
- Validation: original proof re-elaborated; every edge witness kernel-checked in its Lean local context; selected topology compiled as a separate Lean theorem.
- Axioms: `Classical.choice, Quot.sound, propext`
- Concrete certificate: [semantic_graph_certificate.lean](semantic_graph_certificate.lean) embeds the accepted proof and checks every selected raw witness, premise list, and conclusion against this graph.

![dependency graph](graph.svg)

## Hyperedges

| Edge | Premises | Conclusion | Rule | Retrieval |
|---|---|---|---|---|
| `h_goal` | hc₁, hc₂, hc'₁, hc'₂, hcob, hcob', hintertwine | goal | `coboundary_factor_identity + orbit_factor_identity + congrArg` | — |
