# Lean rollout dependency-graph pilot

20 sound, structured rollouts selected under the cohort config. Each graph is extracted from Lean-elaborated proposition bindings; retrieval is an overlay, not a reasoning node.

See [cohort_report.md](cohort_report.md) for sampling, validation layers, distributions, and a compact gallery.

| Graph | Source | Nodes | Edges | Depth | Snapshots excluded | Retrieval matched |
|---|---|---:|---:|---:|---:|---:|
| [exists_coloring_increasing_pairs](graphs/p1925_exists_coloring_increasing_pairs/graph.md) | `2107.05136` | 1 | 1 | 1 | 0 | 1/1 |
| [basel_series](graphs/p1763_basel_series/graph.md) | `math_0506415` | 2 | 2 | 2 | 0 | 2/4 |
| [tanh_ge_one_sub_exp_neg](graphs/p0925_tanh_ge_one_sub_exp_neg/graph.md) | `2209.07782` | 2 | 1 | 1 | 0 | 5/11 |
| [group_symmetrization_lipschitz](graphs/p3260_group_symmetrization_lipschitz/graph.md) | `2302.01915` | 8 | 5 | 4 | 0 | 0/1 |
| [fixed_disc_of_contractivity](graphs/p2061_fixed_disc_of_contractivity/graph.md) | `1901.02623` | 3 | 1 | 1 | 0 | 2/2 |
| [quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter](graphs/p1335_quarter_stratifiable_diagonal_isgdelta_and/graph.md) | `0810.3024` | 5 | 1 | 1 | 0 | 5/7 |
| [abelian_surjective_add_id_star_commute](graphs/p2404_abelian_surjective_add_id_star_commute/graph.md) | `math_0608589` | 1 | 1 | 1 | 0 | 4/4 |
| [two_minimal_missing_faces_deletion](graphs/p0381_two_minimal_missing_faces_deletion/graph.md) | `1701.07720` | 4 | 1 | 1 | 0 | 2/5 |
| [sequence_triangular_formula](graphs/p1318_sequence_triangular_formula/graph.md) | `math_0611410` | 4 | 1 | 1 | 0 | 0/9 |
| [paired_complex_tuple_set_convex](graphs/p1664_paired_complex_tuple_set_convex/graph.md) | `0708.3541` | 6 | 1 | 1 | 0 | 2/6 |
| [linfty_eq_erosion_distance](graphs/p0390_linfty_eq_erosion_distance/graph.md) | `1710.01577` | 1 | 1 | 1 | 0 | 8/22 |
| [not_biorderable_of_product_conjugates_eq_one](graphs/p1572_not_biorderable_of_product_conjugates_eq_o/graph.md) | `1401.0570` | 3 | 1 | 1 | 0 | 1/5 |
| [finite_support_derivation](graphs/p1242_finite_support_derivation/graph.md) | `0811.2405` | 5 | 2 | 2 | 0 | 0/8 |
| [slope_composition_equivalent](graphs/p1489_slope_composition_equivalent/graph.md) | `math_0301015` | 7 | 1 | 1 | 0 | 5/10 |
| [two_bilinear_products_associative_iff](graphs/p0770_two_bilinear_products_associative_iff/graph.md) | `1302.0399` | 1 | 1 | 1 | 0 | 0/1 |
| [intertwining_orbit_cocycle](graphs/p0818_intertwining_orbit_cocycle/graph.md) | `math_0408120` | 8 | 1 | 1 | 0 | 0/2 |
| [substochastic_row_update_product](graphs/p3210_substochastic_row_update_product/graph.md) | `1410.4329` | 9 | 5 | 4 | 0 | 4/16 |
| [antitone_monotone_power_sum_inequality](graphs/p0960_antitone_monotone_power_sum_inequality/graph.md) | `1005.2954` | 15 | 10 | 6 | 0 | 2/17 |
| [finite_product_grid_cell_properties](graphs/p0411_finite_product_grid_cell_properties/graph.md) | `2308.01790` | 1 | 1 | 1 | 0 | 0/10 |
| [seminormal_reesQuotient_iff_radical](graphs/p1789_seminormal_reesquotient_iff_radical/graph.md) | `1207.2891` | 6 | 2 | 2 | 0 | 6/10 |

## Validation boundary

The final submissions and accepted helpers are re-elaborated under Lean/Mathlib 4.29.0. Lean's kernel checks each emitted local witness in its original local context; transient InfoTree bindings with unresolved metavariables are counted and excluded. Dependency fingerprints tie every rendered edge back to checked evidence, and `topology_certificate.lean` proves the selected closure composes to the goal. Every graph also has a self-contained `semantic_graph_certificate.lean`: it embeds the accepted proof and rechecks the selected raw witnesses, exact proposition premises, and conclusions. The reviewed p1662 variant additionally exposes one theorem per selected edge and composes them into the final theorem. This establishes a sound selected-proof projection, not a complete editor trace or a unique/globally minimal mathematical decomposition.
