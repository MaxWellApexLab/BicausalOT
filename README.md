# BicausalOT

A Lean 4 formalization of the Bellman value representation for bicausal optimal
transport, together with the descriptive-set-theoretic results it requires.

## Build status

Builds against **mathlib master `edc39bf7`** (toolchain `v4.33.0-rc1`):
8725 jobs, 0 errors, 0 warnings. 75 of 75 `#print axioms` reports list only
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no custom axioms.

## What is here

**Bicausal optimal transport.** The value of a bicausal transport problem equals
the value of a Bellman recursion — for one period (`bellman_value_eq`) and for a
general finite horizon (`MultiPeriod.bellman_value_eq_multi`), with histories as
nested products and a time-to-go recursion. Two measurable-strategy theorems sit
on top:

* `MultiPeriod.exists_eps_strategy_analyticallyMeasurable` — under Borel Markov
  kernels and lower semianalytic costs, an ε-optimal strategy that is
  σ(Σ¹₁)-measurable at every stage (Bertsekas–Shreve 7.50), and
  `bellman_value_eq_multi_measurable`: restricting the strategy infimum to such
  strategies does not change the value.
* `MultiPeriod.exists_optimal_measurable_strategy` — under Feller kernels and
  lower semicontinuous costs, an *exactly* optimal strategy that is plain-Borel
  measurable, and `bellman_value_attained_measurable`: the Bellman value is
  attained (Bertsekas–Shreve 8.3). Neither theorem dominates the other.

**Descriptive set theory.** The supporting library, none of which is in mathlib:

| Result | Reference |
| --- | --- |
| `jankov_von_neumann` — uniformization of analytic sets by a σ(Σ¹₁)-measurable function | Kechris 18.1 |
| `exists_measurable_selection` — Kuratowski–Ryll-Nardzewski measurable selection | Kechris 12.13 |
| `AnalyticSet.measure_eq_iSup_isCompact` — Choquet capacitability; `AnalyticSet.nullMeasurableSet` — universal measurability | Kechris 30.13, BS 7.42 |
| `ProbabilityMeasure.instPolishSpace` — `P(X)` is Polish for `X` Polish (Lévy–Prokhorov completeness and separability) | Parthasarathy II |
| `lintegral_lowerSemianalytic` — kernel integrals preserve lower semianalyticity | BS 7.48 |
| `IsLowerSemianalytic.iInf_fiber` — fibrewise infima preserve lower semianalyticity | BS 7.47 |
| `MultiPeriod.VGo_isLowerSemianalytic` — value functions are lower semianalytic | BS 8.2 |
| `exists_tendsto_subseq_couplings` — sequential upper hemicontinuity of the couplings correspondence | — |
| `continuous_probabilityMeasure_map_prodMk` — joint continuity of `(x, γ) ↦ γ.map (Prod.mk x)` | — |

## Verifying it

```
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

`lake build` elaborates `BicausalOT/AxiomsAudit.lean`, which runs `#print axioms`
on every headline theorem; `AxiomAudit.lean` at the repository root does the same
for four of them and is meant to be run on its own. Any `sorry` or user-declared
axiom anywhere in a dependency graph would appear in that output.

## Layout

```
BicausalOT/
  Defs, Proposition1, LowerBound, UpperBound, ValueRepresentation, Existence
                                  one-period theory
  MultiPeriod, MultiPeriodTopology, FeasNonempty
                                  general finite horizon
  SemianalyticValue, MeasurableStrategy
                                  Borel model: lower semianalytic values,
                                  σ(Σ¹₁)-measurable ε-optimal strategies
  LscBellman, MeasurableFeasibleStrategy
                                  Feller/lsc model: exact Borel-optimal strategies
  DescriptiveSetTheory/           the supporting library
docs/                             design notes written during development
BLUEPRINT.md                      the development plan and log
```

## References

* D. Bertsekas and S. Shreve, *Stochastic Optimal Control: The Discrete Time
  Case*, Chapters 7–8.
* A. Kechris, *Classical Descriptive Set Theory*.
* K. Parthasarathy, *Probability Measures on Metric Spaces*.

## Methodology

This is an AI-assisted formalization (Max Well Apex): the Lean is AI-generated
under human direction. Every result is verified by a full `lake build` from a
clean environment, `sorry`/custom-axiom scans, and the kernel axiom audit
described above. Responsibility for correctness rests with us.

## License

Apache 2.0.
