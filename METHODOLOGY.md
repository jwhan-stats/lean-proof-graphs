# Methodology: Lean rollout dependency graphs

## Protocol

This pipeline turns a successful Lean rollout into a **sound dependency
hypergraph for one selected proof**.

1. **Select first.** Declare the cohort and seed before inspecting graphs.
2. **Reconstruct.** Keep accepted helper declarations and the verified final
   submission; reject failed verification and unsafe placeholders.
3. **Extract.** Proposition-valued theorem inputs are manifest nodes. A
   metavariable-free local proposition and its proof value form a derived node
   and hyperedge; the proof's direct proposition dependencies are its joint
   premises. Retrieval is provenance, not a reasoning node.
4. **Select and draw.** Take the exact backward closure of the theorem goal and
   render it left-to-right by dependency depth.
5. **Check.** Re-elaborate the proof, kernel-check every emitted edge witness,
   verify its premise/conclusion fingerprint, compile both the selected
   topology and a self-contained concrete replay, and audit transitive axioms.
6. **Report.** Measure graph depth, size, fan-in, side conditions, retrieval
   matches, exclusions, and axioms. Keep rollout events in a separate table.

The result is sound under the declared projection and atomicity policy. It is
not a unique decomposition, a globally minimal proof graph, or a complete
trace of every transient elaboration state.

---

# Appendix

## A. Objects and graph schema

Keep three objects distinct:

1. **Rollout/search tree:** searches, rejected attempts, verifier calls, and
   temporal order.
2. **Accepted Lean proof:** the checked proof term and local contexts.
3. **Dependency hypergraph:** a forward semantic projection used for drawing
   and measurement.

Graph elements:

- **Manifest node:** proposition supplied at the theorem boundary.
- **Derived node:** checked proposition-valued `let`/`have` binding recovered
  from the theorem value or target InfoTree.
- **Hyperedge:** direct proposition free variables of one checked proof value,
  jointly implying its conclusion.
- **Goal:** theorem body after boundary introduction.
- **Selected graph:** backward dependency closure of the goal. Unused accepted
  locals remain in JSON but are not rendered.
- **Rule item:** named declaration used by an edge witness. Mathlib
  declarations are atomic; accepted rollout helpers are atomic and separately
  tagged.
- **Retrieval overlay:** attached only when a returned declaration occurs in
  an edge witness.
- **Excluded snapshot:** target InfoTree binding whose type or witness still
  contains a metavariable. It is recorded with a reason and never emitted as
  an edge.

A small side-condition node such as `lam ≠ 0` is emitted only when the accepted
proof contains (or the checked target InfoTree recovers) a separate local
proposition and witness for it. Such nodes cannot always be manufactured
without changing the proof: when a condition remains internal to a larger
term, the graph keeps that larger step atomic under this projection.

Lean `FVarId`s preserve binder identity; equal-looking propositions are not
automatically merged.

## B. Cohorts

- `config.json`: shortest 20, retained only as a regression smoke test.
- `configs/random100.json`: fixed-seed hash sample for cohort summaries; avoids
  shortest-proof selection bias.
- `configs/coverage48.json`: round-robin sample over `have` count, helper use,
  and retrieval-count strata; intended for visual coverage, not prevalence
  estimates.

Each audit stores the eligible population, strategy, seed, hash ranks, stratum
counts, rejection reasons, and selected rollout IDs.

## C. Verification boundary

1. **Rollout gate:** require successful `verify_submission`; reject `sorry`,
   `admit`, `axiom`, and related warnings/tokens after ignoring comments and
   strings.
2. **Original proof:** re-elaborate accepted helpers and the final theorem with
   pinned Lean/Mathlib 4.29.0.
3. **Edge witness:** in its original local context, require a metavariable-free
   proof value accepted by Lean's kernel whose inferred type is definitionally
   equal to the rendered conclusion.
4. **Projection link:** recheck a SHA-256 record of every edge's Lean premises
   and conclusion.
5. **Topology:** compile `topology_certificate.lean`, which composes exactly the
   selected hyperedges from boundary facts to the goal. The certificate uses
   abstract proposition atoms because concrete edge witnesses were already
   checked in their dependent contexts.
6. **Concrete replay (every graph):** compile
   `semantic_graph_certificate.lean`, which embeds the complete reconstructed
   accepted proof. `#check_dependency_graph` reads its elaborated theorem
   value, kernel-checks every selected local witness, and compares the exact
   raw witness ID, ordered proposition premises, and conclusion with the
   embedded graph manifest. Deterministic source, topology, proof, and
   certificate hashes prevent stale evidence from being accepted.
7. **Expanded reviewed replay (p1662):** additionally expose one executable
   theorem named `edge_<graph-edge-id>` per selected edge, apply each theorem
   at the exact rendered proposition types, and reconstruct the final theorem
   only from those edge theorems.
8. **Axioms:** record `Lean.collectAxioms`; fail on `sorryAx`-like dependencies
   and report classical, quotient, and extensional axioms separately.

Namespace-sensitive sources are checked in the same namespace position used
during extraction; sources originally requiring standalone isolation are
replayed unchanged as standalone files. The mode is recorded in provenance.
Only compiler-generated binder names containing source paths are
canonicalized; raw witness IDs, proposition types, and dependency order remain
exact.

## D. Rendering and analysis

Render only the selected closure:

- teal: manifest premises;
- orange: derived facts and hyperedge diamonds;
- green: goal;
- gray: side conditions;
- dashed purple: retrieval provenance.

Use one row per graph for depth, size, fan-in, side conditions, exclusions, and
axioms; one row per selected edge for rule/retrieval analysis; and a separate
event table for searches and rejected attempts. Depth is relative to the
declared manifest and atomicity policy, so report it with size and fan-in.

## E. Claim limits

The pipeline does not establish:

- uniqueness or global minimality;
- task-level necessity of each theorem hypothesis;
- absence of a different or shorter proof;
- completeness over transient tactic/elaboration bindings;
- semantic equivalence of separately bound but similar-looking propositions;
- causal effects of retrieval on success.

Those require separate premise-removal, alternative-proof, normalization, and
experimental audits.
