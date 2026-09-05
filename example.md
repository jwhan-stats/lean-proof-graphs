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
