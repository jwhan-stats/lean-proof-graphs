# When Does a Lean `have` Become an Intermediate Graph Node?

This note explains the current dependency-graph projection through four worked
examples.  In every example, the yellow/orange rectangular nodes are derived
propositions.  A yellow/orange diamond is a hyperedge (a proof step), not an
intermediate proposition.

The most important distinction is:

> A `have` written in the Lean source is not automatically a visible graph
> node.  It must first survive as admissible elaborated evidence, and then it
> must lie in the backward dependency closure of the goal.

## The three decisions made by the pipeline

### 1. Is the local fact an admissible proposition?

A local binding can produce an edge only when:

- its type is a proposition (`Prop`);
- its type and proof contain no unresolved metavariables;
- Lean's kernel accepts the proof in its exact local context; and
- the inferred proof type is definitionally equal to the stated proposition.

Consequently, useful definitions such as `let A : ℝ := ...` are not graph
nodes: `A` is data, not a proposition.

### 2. Where is the binding recovered from?

The exporter first examines the outer `lambda`/`let` telescope of the accepted
theorem value.  A proposition-valued `have` that remains on this outer spine is
recorded as a `theorem_value_telescope` edge.

If the theorem-value telescope contains no derived proposition bindings, the
pipeline falls back to kernel-checked local bindings recovered from Lean's
target InfoTree.  If the telescope does contain derived bindings, InfoTree-only
bindings are retained as raw evidence but are not merged into the projected
graph.

This means that a nested fact can remain inside the proof witness for a larger
outer fact without becoming a node of its own.

### 3. Is the admitted fact needed by the selected goal derivation?

For every checked witness, the exporter records the proposition-valued free
variables that the witness directly references.  The projection starts at the
goal and repeatedly follows these direct dependencies backwards.  Only nodes
and hyperedges reached by this traversal receive `selected: true` and appear in
the rendered graph.

This last step is a reachability test, not a judgment of mathematical
importance.  A source-level `have` may be helpful to the author and still be
absent from the selected graph.  Conversely, a tactic certificate may retain a
dependency that a human proof would regard as redundant.  The selected graph
is sound for this particular proof term, but it is not claimed to be a minimal
mathematical proof.

## Summary of the examples

| Example | Pattern in the target theorem | Derived candidates in `graph.json` | Selected derived nodes | Main lesson |
|---|---:|---:|---:|---|
| `p0381` | 9 source `have`s, all inside a contradiction proof | 9 | 0 | InfoTree can see local facts even when the final goal edge absorbs the whole argument. |
| `p1242` | 1 outer `have` | 1 | 1 | A retained fact used directly by the rest of the proof becomes a clean node. |
| `p1067` | 7 outer `have`s plus nested temporary facts | 7 | 5 | A retained candidate can be unselected, and nested facts can stay inside a larger edge. |
| `p0960` | 9 outer `have`s plus one branch-local `have` | 9 | 9 | A top-level chain can be preserved almost exactly while a branch-local fact is folded into its parent edge. |

## Meeting note: sensitivity to proof-writing style

The graph depends strongly on how the LLM writes the Lean proof.  It is a
graph of one accepted proof term, not a canonical graph of the mathematical
argument.  Two proofs can use the same mathematical idea but produce graphs
with very different sizes and depths.

For example, `p0381` puts every intermediate fact inside `by_contra`:

```lean
by_contra hSK
have hLmin := ...
have hwS := ...
exact contradiction
```

Those facts are local to the contradiction subproof.  The current exporter
folds that whole subproof into one goal edge, so none of its nine recovered
`have`s is selected.

The same argument could instead be organized schematically as outer facts:

```lean
have hbad_implies_w : S ∉ K → w ∈ S := by ...
have hnot_bad : ¬ S ∉ K := by ...
exact Classical.byContradiction hnot_bad
```

This version is likely to produce visible nodes such as `hbad_implies_w` and
`hnot_bad`, even though the mathematical argument has not changed.

Helper boundaries have the same effect.  In `p1242`, the main theorem graph is
small because the finite-support construction is inside an atomic helper.  If
the helper body were written inline, the graph would be much larger.

This matters when graph size, depth, or node count is used to compare LLMs:
a difference may reflect coding style (`by_contra`, helper extraction, or
inlining) rather than a difference in mathematical reasoning quality.

The main design question for discussion is therefore:

> Should the graph represent the exact Lean proof written by the LLM, or a
> normalized mathematical argument that is less sensitive to Lean coding
> style?

The current pipeline answers the first question.  Answering the second would
require an additional normalization step, nested-subproof expansion, or
paper-level semantic annotations.

---

## Example 1: `p0381_two_minimal_missing_faces_deletion`

- [Lean proof](outputs/candidates/p0381_two_minimal_missing_faces_deletion/proof.lean)
- [Graph data](outputs/graphs/p0381_two_minimal_missing_faces_deletion/graph.json)
- [Rendered graph](outputs/graphs/p0381_two_minimal_missing_faces_deletion/graph.svg)

### Statement in plain English

Assume that the only inclusion-minimal subsets of the finite interval
`{1, ..., m}` that do not belong to `K` are `I` and `J`.  If `w` belongs to
both `I` and `J`, then every subset of `{1, ..., m}` that avoids `w` must
belong to `K`.

### Lean proof and natural-language proof side by side

| Lean step | Natural-language meaning |
|---|---|
| `by_contra hSK` | Suppose, for contradiction, that the chosen set `S` does not belong to `K`. |
| `let C := {T | T ⊆ Icc 1 m ∧ T ∉ K ∧ T ⊆ S}` | Consider all bad subsets of `S`: subsets that stay in the interval but are not in `K`. |
| `have hSV : S ⊆ Icc 1 m := ...` | Since `S` is contained in the interval with `w` removed, it is contained in the interval itself. |
| `have hCfinite : C.Finite := ...` | The interval is finite, so its collection of subsets is finite; therefore `C` is finite. |
| `have hCnonempty : C.Nonempty := ...` | The set `S` itself is in `C`, so `C` is nonempty. |
| `obtain ⟨L, hLminC⟩ := hCfinite.exists_minimal hCnonempty` | Choose an inclusion-minimal bad subset `L` of `S`. |
| `have hLmin : Minimal (...) L := ...` | Show that `L` is not merely minimal inside `C`; it is a globally minimal missing face.  The nested `hTC` verifies that any smaller bad `T` also belongs to `C`. |
| `rcases (hmissing L).mp hLmin with hLI \| hLJ` | By the classification hypothesis, `L` is either `I` or `J`. |
| `have hwL : w ∈ L := ...` | In either branch, `w ∈ L`, because `w` lies in both `I` and `J`. |
| `have hwS : w ∈ S := hLminC.1.2.2 hwL` | Since `L ⊆ S`, it follows that `w ∈ S`. |
| `exact (hS hwS).2 rfl` | But `S` was assumed to avoid `w`.  This contradiction proves `S ∈ K`. |

### What happened to each `have`?

| Source `have` | Raw source | Selected? | Explanation |
|---|---|---:|---|
| `hSV : S ⊆ Set.Icc 1 m` | InfoTree | No | The final theorem witness contains the argument internally and does not reference this InfoTree `FVarId`. |
| `hCfinite : C.Finite` | InfoTree | No | Same: it is checked raw evidence, but there is no selected edge from the goal to this local identity. |
| `hCnonempty : C.Nonempty` | InfoTree | No | Checked but outside the selected free-variable closure. |
| `hTC : T ∈ C` | InfoTree, nested inside `hLmin` | No | It is an internal step in the witness for `hLmin`. |
| `hLmin : Minimal (...) L` | InfoTree | No | It remains visible in the InfoTree, but not as a direct free variable of the final theorem body. |
| first `hwL : w ∈ L` | InfoTree, `L = I` branch | No | Branch-local proof folded into the final witness. |
| first `hwS : w ∈ S` | InfoTree, `L = I` branch | No | Branch-local proof folded into the final witness. |
| second `hwL : w ∈ L` | InfoTree, `L = J` branch | No | Distinct `FVarId`, despite having the same printed name and statement. |
| second `hwS : w ∈ S` | InfoTree, `L = J` branch | No | Distinct branch-local binding, also folded into the final witness. |

The crucial source shape is that all these facts occur under `by_contra`.
In the elaborated theorem value, the contradiction function contains the local
argument internally rather than exposing these facts on the theorem's outer
`let` telescope.  The InfoTree fallback recovers nine checked derived
candidates, but the final edge has only three direct proposition dependencies:

```text
hmissing   hw   hS
    \       |   /
       h_goal
          |
      goal: S ∈ K
```

Thus the compact graph has 4 selected nodes and 1 selected hyperedge.  The
artifact still stores 26 node records and 10 checked hyperedges in total; the
rest simply have `selected: false`.

---

## Example 2: `p1242_finite_support_derivation`

- [Lean proof](outputs/candidates/p1242_finite_support_derivation/proof.lean)
- [Graph data](outputs/graphs/p1242_finite_support_derivation/graph.json)
- [Rendered graph](outputs/graphs/p1242_finite_support_derivation/graph.svg)

### Statement in plain English

Suppose membership in `D S` always has a finite witness contained in `S`.  If
`P` belongs to the `n`-fold iterate of `D` applied to `A`, then there is a
finite-support chain witnessing how `P` can be derived through those `n`
iterations.

### Lean proof and natural-language proof side by side

| Lean step | Natural-language meaning |
|---|---|
| `have hsub : {P} ⊆ (D^[n]) A := ...` | Turn the point-membership assumption `P ∈ Dⁿ(A)` into the singleton inclusion `{P} ⊆ Dⁿ(A)`. |
| `finite_support_chain_forall ... {P} ... hsub` | Apply the previously proved helper theorem to the finite set `{P}`.  This produces a sequence of finite supports together with all chain properties. |
| `rcases ... with ⟨S, hSfin, hSsub, hStop, hSchain⟩` | Unpack the sequence and its properties. |
| `exact ⟨S, hSfin, hSsub, hStop rfl, hSchain⟩` | Specialize the top-set inclusion to the unique member `P` and assemble the requested conclusion. |

### Why `hsub` is a node

The outer `have hsub` survives on the theorem-value telescope.  The subsequent
application of `finite_support_chain_forall` directly references `hsub`, so it
also lies in the backward closure of the goal:

```text
hP --------------------> hsub : {P} ⊆ Dⁿ(A)
                             |
hD -----------\             |
hn ------------+---------- h_goal ----------> goal
```

| Source `have` in the target theorem | Raw source | Selected? | Explanation |
|---|---|---:|---|
| `hsub : {P} ⊆ (D^[n]) A` | Theorem-value telescope | Yes | It is a checked outer proposition binder and the rest of the proof directly uses it. |

The large helper theorem `finite_support_chain_forall` has many internal
`have`s, but accepted rollout helpers are atomic under the current projection.
Those helper-internal facts are therefore outside this target theorem's node
boundary.

---

## Example 3: `p1067_complex_exp_modulus_bounds`

- [Lean proof](outputs/random100/candidates/p1067_complex_exp_modulus_bounds/proof.lean)
- [Graph data](outputs/random100/graphs/p1067_complex_exp_modulus_bounds/graph.json)
- [Rendered graph](outputs/random100/graphs/p1067_complex_exp_modulus_bounds/graph.svg)

### Statement in plain English

Let

```text
f(z) = z + 1 + exp(-z).
```

In the region where `x = -Re(z)` is at least both `‖z‖/2` and `3`, the
exponential term dominates the linear term `z + 1`.  Consequently,

```text
(1/2) exp(x) ≤ ‖f(z)‖ ≤ 2 exp(x).
```

### Lean proof and natural-language proof side by side

| Lean step | Natural-language meaning |
|---|---|
| `have hx3 : 3 ≤ -z.re := hz.2` | Record the lower bound `x ≥ 3`. |
| `have hnormz : ‖z‖ ≤ 2 * (-z.re) := ...` | Rewrite the other regional assumption as `‖z‖ ≤ 2x`. |
| `have hexp : 4 * (-z.re) + 2 ≤ exp (-z.re) := ...` | Use a finite Taylor lower bound for the exponential to show `exp(x) ≥ 4x + 2` when `x ≥ 3`. |
| `have hz1 : ‖z + 1‖ ≤ (1/2) * exp (-z.re) := ...` | From `‖z+1‖ ≤ ‖z‖+1`, the region assumption, and the exponential estimate, show that the non-exponential part is at most half of `exp(x)`. |
| `have hnormexp : ‖Complex.exp (-z)‖ = exp (-z.re) := ...` | Use the standard identity `‖eʷ‖ = e^(Re w)` with `w = -z`. |
| `have hlower_core : (1/2) * exp (-z.re) ≤ ‖z+1+exp(-z)‖ := ...` | The reverse triangle inequality gives `‖a+b‖ ≥ ‖b‖-‖a‖`; use `a=z+1`, `b=exp(-z)`. |
| `have hupper_core : ‖z+1+exp(-z)‖ ≤ 2 * exp (-z.re) := ...` | The ordinary triangle inequality gives an upper bound by `‖z+1‖+‖exp(-z)‖`, which is at most `3/2 exp(x)` and hence at most `2 exp(x)`. |
| `exact ⟨hlower_core, hupper_core⟩` | Combine the lower and upper estimates. |

### Selected and unselected outer `have`s

| Outer `have` | Candidate? | Selected? | Exact reason |
|---|---:|---:|---|
| `hx3` | Yes | No | It survives on the telescope, but no selected later witness directly references its `FVarId`; the generated arithmetic proofs use `hz` instead. |
| `hnormz` | Yes | No | It also survives, but the checked witness for `hz1` directly depends on `hz` and `hexp`, not on the `hnormz` binder. |
| `hexp` | Yes | Yes | `hz1` and the checked upper-bound witness depend on it. |
| `hz1` | Yes | Yes | Both core norm bounds depend on it. |
| `hnormexp` | Yes | Yes | Both core norm bounds use the exponential norm identity. |
| `hlower_core` | Yes | Yes | The final conjunction directly references it. |
| `hupper_core` | Yes | Yes | The final conjunction directly references it. |

The selected graph is:

```text
hz ----------------------> hexp
hz + hexp ---------------> hz1
(closed Mathlib fact) ----> hnormexp
hz1 + hnormexp ----------> hlower_core
hz + hexp + hz1
   + hnormexp -----------> hupper_core
hlower_core
   + hupper_core --------> goal
```

The source also contains temporary nested facts `h`, `hsum`, `hrev`, `hrev'`,
and `htri`.  Lean's InfoTree records them, but they occur inside the witnesses
for `hnormz`, `hexp`, `hlower_core`, or `hupper_core`.  Because this theorem
already has theorem-value-telescope edges, the current policy does not merge
those InfoTree-only bindings.  Their reasoning is still kernel-checked as part
of the corresponding larger edge witness.

This example also shows why `selected` does not mean mathematically minimal.
For example, the recorded witness for `hupper_core` contains direct references
to `hz`, `hexp`, `hz1`, and `hnormexp`, even though a cleaned-up paper proof
could present the upper bound using fewer named facts.

---

## Example 4: `p0960_antitone_monotone_power_sum_inequality`

- [Lean proof](outputs/candidates/p0960_antitone_monotone_power_sum_inequality/proof.lean)
- [Graph data](outputs/graphs/p0960_antitone_monotone_power_sum_inequality/graph.json)
- [Rendered graph](outputs/graphs/p0960_antitone_monotone_power_sum_inequality/graph.svg)

### Statement in plain English

For a nonnegative decreasing sequence `a` and a nonnegative increasing
sequence `b`, compare four weighted sums:

```text
A = Σ aᵢˢ,        B = Σ aᵢ² bᵢ,
C = Σ aᵢˢ⁺¹,      D = Σ aᵢ bᵢ.
```

The theorem proves `A * B ≤ C * D`.  Its strategy is to expand the
difference into a double sum of pairwise nonnegative terms.

### Lean proof and natural-language proof side by side

| Lean step | Natural-language meaning |
|---|---|
| `let A`, `let B`, `let C`, `let D` | Give short names to the four sums in the target inequality.  These are real numbers, not proposition nodes. |
| `let U`, `let V`, `let W` | Define pairwise summands so that `W i j = U i j + U j i - V i j - V j i`.  These are functions/data, not proposition nodes. |
| `have hWnonneg : ∀ i j, 0 ≤ W i j := ...` | Compare `i` and `j`.  Since `a` decreases while `b` increases, the pairwise rearrangement lemma makes every symmetric term `W i j` nonnegative. |
| `have hsumW : 0 ≤ Σ i, Σ j, W i j := ...` | A sum of nonnegative pairwise terms is nonnegative. |
| `have hU ... = C * D` and `have hUs ... = C * D` | Factor the two orientations of the `U` double sum as the product `C * D`; swapping the summation indices changes nothing. |
| `have hV ... = A * B` and `have hVs ... = A * B` | Similarly factor both orientations of the `V` double sum as `A * B`. |
| `have hsumEq : Σ i, Σ j, W i j = 2 * (C*D - A*B)` | Substitute the four factorizations into the definition of `W` and simplify. |
| `have hdiff : 0 ≤ C*D - A*B := by nlinarith` | Combine nonnegativity of the double sum with its exact value. |
| `have hle : A*B ≤ C*D := sub_nonneg.mp hdiff` | Rewrite nonnegativity of the difference as the desired inequality. |
| `simpa [A, B, C, D] using hle` | Expand the abbreviations and finish the original statement. |

### Which `have`s became nodes?

All nine outer proposition-valued `have`s survive on the theorem-value
telescope and lie in the selected goal closure:

| Outer `have` | Selected? | Direct role in the graph |
|---|---:|---|
| `hWnonneg` | Yes | Supplies pointwise nonnegativity to `hsumW`. |
| `hsumW` | Yes | One premise of `hdiff`. |
| `hU` | Yes | Used by `hUs` and `hsumEq`. |
| `hUs` | Yes | Used by `hsumEq`. |
| `hV` | Yes | Used by `hVs` and `hsumEq`. |
| `hVs` | Yes | Used by `hsumEq`. |
| `hsumEq` | Yes | The other premise of `hdiff`. |
| `hdiff` | Yes | Used to derive `hle`. |
| `hle` | Yes | Used directly by the final goal proof. |

Their dependency structure is approximately:

```text
assumptions -> hWnonneg -> hsumW ---------\
                                                -> hdiff -> hle -> goal
hU -> hUs --\                              /
               -> hsumEq -----------------
hV -> hVs --/
```

Inside the proof of `hWnonneg`, however, one branch contains:

```lean
have hswap := antitone_monotone_power_sum_pair_nonneg ...
```

`hswap` is visible in the InfoTree but is not an outer theorem-value-telescope
binding.  It is therefore folded into the single checked edge whose conclusion
is `hWnonneg`.  This gives a useful hierarchy:

- `hWnonneg` is a reusable top-level logical milestone and becomes a node;
- `hswap` is a branch-local implementation detail inside the proof of that
  milestone and remains inside its edge witness.

The accepted helper `antitone_monotone_power_sum_pair_nonneg` is also treated
atomically.  Its own internal `have`s do not become nodes in the graph of the
main theorem.

---

## Cross-check against the original arXiv proofs

The preceding sections explain whether the projection is faithful to the
*accepted Lean proof term*.  That is different from asking whether it recovers
the mathematical milestones chosen by the paper's author.  To check the
second question, the four examples were compared with the corresponding
proofs in the source papers.

For this comparison, an intermediate result is classified as one of:

- **paper-explicit**: the paper states the result as a displayed line, lemma,
  or explicit sentence in the proof;
- **equivalent regrouping**: the Lean proof packages one or more paper steps
  into a mathematically equivalent bound or identity; or
- **Lean-only scaffolding**: the fact is useful for elaboration, finite-sum
  manipulation, type conversion, or helper reuse, but is not a milestone in
  the paper proof.

These labels are a semantic audit of the examples, not inputs to the current
rule-based exporter.

### Overall result

| Example | Source proof | Paper/graph alignment | Assessment |
|---|---|---|---|
| `p0381` | [Lemma 3.3 of arXiv:1701.07720](https://arxiv.org/html/1701.07720v3) | Low | The paper exposes a short contradiction chain, whereas the selected graph contracts the whole chain into one goal edge. |
| `p1242` | [Section 2, equations (2.10)--(2.11), of arXiv:0811.2405](https://arxiv.org/pdf/0811.2405#page=4) | Low at the main-theorem boundary; high inside the helper | The only selected node is a singleton adapter.  The paper-aligned backward finite-support construction is hidden in atomic helpers. |
| `p1067` | [Lemma 3.3, equation (3.2), of arXiv:1510.07449](https://arxiv.org/pdf/1510.07449#page=7) | High | The selected nodes preserve exponential dominance, the exponential norm identity, and the two triangle-inequality bounds. |
| `p0960` | [Lemma 2.2, equation (2.20), of arXiv:1005.2954](https://arxiv.org/pdf/1005.2954#page=11) | Medium | Lean uses a symmetric double-sum proof instead of the paper's induction, but its pairwise nonnegativity lemma contains essentially the same factorization. |

### `p0381`: the paper milestones are real, but all are contracted

The source paper first says that it is enough to prove that
`K \ w` has no missing face.  It then assumes that a face `sigma` is missing
from `K \ w`, observes that `sigma` is also missing from `K`, and uses the fact
that every missing face contains one of the two minimal missing faces.  This
is impossible: `sigma` avoids `w`, while both minimal missing faces contain
`w`.

The correspondence with the Lean proof is:

| Paper step | Lean realization | Current selected node? | Classification |
|---|---|---:|---|
| A missing face of the deletion is a missing face of the original complex. | `hSK`, together with `hSV` and the representation of `S` | No | paper-explicit |
| The bad face contains a minimal missing face. | Construct finite `C`, choose `L`, and prove `hLmin` | No | paper-implicit justification made explicit by Lean |
| That minimal face is `I` or `J`. | `(hmissing L).mp hLmin` | No | paper-explicit |
| Therefore the bad face contains `w`, a contradiction. | `hwL`, `hwS`, and the final contradiction | No | paper-explicit |

The finite minimization through `C` is longer than the paper because the Lean
hypothesis classifies only *minimal* missing faces.  It supplies the omitted
justification for the paper's assertion that an arbitrary missing face
contains a minimal one.  Consequently, selecting none of `hLmin`, `hwL`, or
`hwS` is correct for the current direct-`FVarId` rule, but it is too coarse for
a paper-facing proof graph.  At minimum, the existence/classification of `L`
and the resulting occurrence of `w` would be sensible semantic cut points.

### `p1242`: the paper proof is hidden behind the helper boundary

The paper starts with `P in T_n(A)` and constructs finite supports backwards.
It first chooses a finite `F_(n-1)` that derives `P`.  For every formula in
that finite set, it chooses another finite support one level earlier, takes
their finite union, and repeats until reaching `S_0`.

That is almost exactly the organization of the two accepted Lean helpers:

| Paper operation | Lean realization | Visible in the main graph? |
|---|---|---:|
| Perform one finite-support pullback through `D`. | `finite_support_of_derivation` | No; helper treated atomically |
| Repeat the pullback down the derivation levels. | induction in `finite_support_chain_forall` | No; helper treated atomically |
| Apply the construction to the final formula `P`. | replace `P` by the finite singleton `{P}` using `hsub` | Yes |

Thus `hsub : {P} ⊆ D^n(A)` is a legitimate dependency in this Lean
implementation, but it is Lean-only scaffolding rather than the paper's main
intermediate result.  The segmentation becomes strongly paper-aligned only
if accepted helpers are expanded one level or represented as compound nodes
with inspectable subgraphs.

### `p1067`: the graph closely follows the displayed calculation

Writing `t = -Re(z)`, the paper proves the lower bound by the chain

```text
|f(z)| >= exp(t) - 1 - |z|
       >= exp(t) - 1 - 2t
       >= (1/2) exp(t),
```

and proves the upper bound with the corresponding ordinary triangle
inequality.  It uses `exp(t) / 2 >= 1 + 2t` for `t >= 3` and
`exp(t) >= 1 + 2t` for `t >= 2`.

| Lean fact | Relation to the paper | Classification |
|---|---|---|
| `hexp : 4*t + 2 <= exp(t)` | A single stronger scalar estimate that implies both estimates used by the paper. | equivalent regrouping |
| `hz1 : ‖z+1‖ <= exp(t)/2` | Packages `‖z+1‖ <= ‖z‖+1 <= 2t+1` and the scalar exponential estimate. | equivalent regrouping |
| `hnormexp : ‖exp(-z)‖ = exp(t)` | The equality used explicitly in both displayed calculations. | paper-explicit |
| `hlower_core` | The paper's reverse-triangle lower-bound calculation. | paper-explicit |
| `hupper_core` | The paper's triangle-inequality upper-bound calculation. | paper-explicit |

The unselected `hx3` and `hnormz` merely restate the two hypotheses.  Omitting
them as separate milestones is reasonable here.  The nested `hrev` and `htri`
are also safely folded into `hlower_core` and `hupper_core`: their parent nodes
still correspond directly to the two halves of the paper proof.  Of these
four examples, this is the clearest evidence that the current projection can
recover a useful paper-level graph when the Lean proof follows the source
calculation and does not outsource its core argument to helpers.

### `p0960`: the local algebra agrees, but the global proof architecture differs

The paper proves the inequality by induction on the sequence length.  After
assuming the result for `k = m`, it expands the difference for `m + 1`, applies
the induction hypothesis, and factors the remaining expression into a sum of
nonnegative terms of the form

```text
a_(m+1) * a_i
* (b_(m+1) * a_i^(s-1) - b_i * a_(m+1)^(s-1))
* (a_i - a_(m+1)).
```

The Lean proof instead proves every ordered-pair contribution nonnegative and
then sums over all pairs.  The hidden helper
`antitone_monotone_power_sum_pair_nonneg` factors a pair into the same three
essential nonnegative pieces: two nonnegative `a` factors, a decreasing-`a`
difference, and a weighted power difference controlled by increasing `b`.
So `hWnonneg` captures the mathematical heart of the paper's factorization,
even though the proof is not inductive.

The remaining selected facts have a different status:

| Selected facts | Role | Classification relative to the paper |
|---|---|---|
| `hWnonneg` | Pairwise positivity behind the inequality | mathematically aligned, but reorganized |
| `hsumW` | Sum the pairwise inequalities | alternative-proof step |
| `hU`, `hUs`, `hV`, `hVs`, `hsumEq` | Convert the symmetric double sum into `2 * (C*D - A*B)` | Lean/alternative-proof scaffolding; absent from the paper |
| `hdiff`, `hle` | Turn nonnegativity of the difference into the target order | routine logical/algebraic closure |

Therefore all nine selected nodes are valid nodes for the *Lean proof that was
actually generated*, but the graph should not be described as a reconstruction
of the paper's trajectory.  A paper-faithful graph would instead expose the
base case, induction hypothesis, `m+1` expansion, factorization, and final
nonnegativity argument.

### Conclusion of the source audit

The node distinction is mechanically sound, but it is not by itself a test of
paper-level mathematical salience.  The examples reveal three independent
sources of disagreement with a paper proof:

1. **scope contraction** can hide a whole local contradiction (`p0381`);
2. **atomic helper boundaries** can hide the actual argument and retain only
   an adapter node (`p1242`); and
3. **a different valid proof** can create a genuinely different graph
   (`p0960`).

When none of these occurs, the current rule can align well with a source proof
(`p1067`).  If paper alignment is an evaluation goal, it should therefore be
measured separately from proof-term faithfulness, ideally with annotations for
paper-explicit, paper-implicit, and formalization-only steps.

---

## Practical interpretation rules

When reading one of these graphs, use the following vocabulary:

| Status | Meaning |
|---|---|
| Not present in `raw_graph.json` | The source construct was not an admissible proposition binding under the extraction policy, or it was outside the theorem boundary being analyzed. |
| Present only as an InfoTree local edge | Lean observed and checked the local fact during elaboration, but it was not retained on the preferred outer theorem-value telescope. |
| Present in `graph.json` with `selected: false` | It is an admitted graph candidate, but the goal's selected direct-dependency closure does not reach it. |
| Present in `graph.json` with `origin: "derived"` and `selected: true` | It is a rendered yellow/orange intermediate proposition node. |

The shortest reliable test is therefore not "does the source contain
`have`?" but:

```text
Did Lean expose a checked proposition binder,
and does a selected downstream witness directly reference that binder's FVarId?
```

That rule explains all four examples above.
