# BicausalOT — A Machine-Verified Bellman Recursion for Bicausal Optimal Transport

**Lean 4 (`v4.29.0-rc8`) · Mathlib (pinned) · 0 `sorry` · 0 custom axioms · 32/32 kernel axiom audits clean**

This repository contains a Lean 4 formalization, on top of Mathlib, of the
dynamic-programming (Bellman) value representation for *bicausal optimal
transport* in discrete time: the infimum of the total transport cost over
bicausal couplings — an initial coupling of the time-0 marginals together with
a family of one-step feasible transition plans — equals the infimum, over
initial couplings only, of the integrated Bellman value function. The theorem
is proved first for a single transition step (`bellman_value_eq`, horizon
T = 1) and then for an arbitrary finite horizon (`MultiPeriod.bellman_value_eq_multi`,
general T), with costs valued in `ℝ≥0∞`, arbitrary (non-measurable) strategy
families, and explicit ε-optimal pointwise selection — so no
measurable-selection machinery is needed for the value representation itself.
Supporting the campaign — and of independent interest — is a self-contained
**descriptive-set-theory library**: Choquet capacitability of analytic sets,
universal measurability of analytic sets, parametrized capacitability for
kernels, integration of lower semianalytic functions along Borel kernels
(Bertsekas–Shreve Prop. 7.48), the Jankov–von Neumann uniformization theorem
(Kechris Thm. 18.1), and a proof that the space of Borel probability measures
on a Polish space is itself Polish — including **completeness and separability
of the Lévy–Prokhorov metric** and the comparison of the Giry σ-algebra with
the Borel σ-algebra of the weak topology, none of which are in Mathlib at the
pinned revision. Every theorem is machine-checked by the Lean kernel with zero
`sorry` and zero user-declared axioms.

---

## 1. What is proved

### 1.1 One-step value representation (`bellman_value_eq`)

Setting: measurable spaces `X₀ X₁ Y₀ Y₁`; probability measures
`μ₀ ∈ P(X₀)`, `ν₀ ∈ P(Y₀)`; *arbitrary* transition families
`κ_μ : X₀ → M(X₁)`, `κ_ν : Y₀ → M(Y₁)`; *arbitrary* cost functions
`c₀ : X₀ × Y₀ → [0,∞]` and `c₁ : (X₀ × Y₀) × (X₁ × Y₁) → [0,∞]`
(no measurability is assumed anywhere — the lower Lebesgue integral `∫⁻`
is defined for arbitrary integrands, and ε-optimal selections are pointwise).

Write `Π(μ₀, ν₀)` for the set of couplings of the initial marginals
(`CouplingSet₀`) and, for `z₀ = (x₀, y₀)`,

```
Γ(z₀) := { γ ∈ M(X₁ × Y₁) | γ ∘ fst⁻¹ = κ_μ(x₀),  γ ∘ snd⁻¹ = κ_ν(y₀) }
```

(`FeasibleSet₀`). Assume each `Γ(z₀)` is nonempty and every
`γ₀ ∈ Π(μ₀, ν₀)` has mass ≤ 1. Then

```
  inf { totalCost(γ₀, γ₁) : γ₀ ∈ Π(μ₀,ν₀), γ₁(z₀) ∈ Γ(z₀) ∀ z₀ }
= inf { ∫ V₀(z₀) dγ₀(z₀)  : γ₀ ∈ Π(μ₀,ν₀) }
```

where

```
totalCost(γ₀, γ₁) = ∫ [ c₀(z₀) + ∫ c₁(z₀, z₁) dγ₁(z₀)(z₁) ] dγ₀(z₀)
V₀(z₀)            = c₀(z₀) + inf { ∫ c₁(z₀,·) dγ : γ ∈ Γ(z₀) } .
```

The left-hand side is exactly the bicausal transport cost: Proposition 1
(`kernel_decomp_implies_bicausal` / `bicausal_implies_decomp`) identifies
bicausal couplings of the two-step processes with kernel decompositions
`(γ₀, γ₁)` where `γ₀ ∈ Π(μ₀, ν₀)` and `γ₁(z₀) ∈ Γ(z₀)` for `γ₀`-a.e. `z₀`.

### 1.2 General finite horizon (`MultiPeriod.bellman_value_eq_multi`)

Setting: processes `X t`, `Y t` (`t ∈ ℕ`, each a measurable space);
nested-product histories `PairHist t`; conditional one-step transition
families `κμ t : XHist t → M(X (t+1))` (assumed probability-valued) and
`κν t : YHist t → M(Y (t+1))`; stage costs `c t : PairHist t → [0,∞]`.
One-step feasible sets `Feas t h` couple the conditional marginals
`κμ t (projX h)` and `κν t (projY h)`; a *strategy* is an arbitrary function
family `γ : (t : ℕ) → PairHist t → M(X (t+1) × Y (t+1))`. The cost-to-go and
Bellman value are defined by time-to-go recursion:

```
costGo 0 t h     = c t h
costGo (k+1) t h = c t h + ∫⁻ z, costGo k (t+1) (h, z) ∂(γ t h)

VGo 0 t h     = c t h
VGo (k+1) t h = c t h + inf { ∫⁻ z, VGo k (t+1) (h, z) ∂γm : γm ∈ Feas t h }
```

**Theorem.** If `μ₀, ν₀` are probability measures, every `κμ t x` is a
probability measure, and every `Feas t h` is nonempty, then for every
horizon `T : ℕ`:

```
  inf_{γ₀ ∈ Π(μ₀,ν₀)} inf_{γ feasible strategy} ∫⁻ costGo T 0 h₀ dγ₀(h₀)
= inf_{γ₀ ∈ Π(μ₀,ν₀)} ∫⁻ VGo T 0 h₀ dγ₀(h₀) .
```

The proof constructs, for each ε > 0, a strategy that is `ε/T`-optimal at the
time-consistent depth of every stage (`exists_eps_strategy`) and shows by
backward induction that it overshoots the Bellman value by at most `k·ε` over
`k` remaining periods (`costGo_le_VGo_add`); the reverse inequality is the
pointwise bound `VGo_le_costGo`. For background on dynamic programming for
causal/bicausal transport see e.g. Backhoff-Veraguas, Beiglböck, Lin &
Zalashko, *Causal transport in discrete time and applications* (SIAM J.
Optim., 2017).

### 1.3 Descriptive-set-theory library

Developed to support the measurable-selection program (Bertsekas–Shreve
Chapter 7 analogues), and reusable on its own:

- **Choquet capacitability** for analytic sets in Polish spaces:
  `μ(A) = sup { μ(K) : K ⊆ A compact }` for finite Borel `μ`
  (Kechris Thm. 30.13, measure case; BS Prop. 7.42), via an explicit Souslin
  scheme over Baire-space cylinders — no abstract capacity theory needed.
- **Universal measurability**: analytic sets are null-measurable for every
  finite Borel measure (Lusin; BS Prop. 7.42).
- **Parametrized capacitability**: for `A` analytic in `X × Y` and a finite
  Borel kernel `κ`, `x ↦ κ x (A_x)` is upper semianalytic (BS Prop. 7.46).
- **Kernel integration** (BS Prop. 7.48): `x ↦ ∫⁻ y, f(x,y) ∂(κ x)` is lower
  semianalytic for lower semianalytic `f` and Borel-measurable Markov `κ`.
- **Jankov–von Neumann uniformization** (Kechris Thm. 18.1): every analytic
  `P ⊆ X × Y` admits a σ(Σ¹₁)-measurable uniformizing function, built from an
  explicit leftmost-branch selector.
- **`P(Ω)` is Polish** for `Ω` Polish (`ProbabilityMeasure.instPolishSpace`):
  Mathlib supplies the Lévy–Prokhorov metric and Prokhorov's theorem; this
  repository supplies the missing **completeness** (Cauchy ⇒ uniformly tight
  ⇒ convergent subsequence) and **separability** (normalized natural-weight
  Dirac mixtures over a countable dense set are `3ε`-dense in
  Lévy–Prokhorov distance).
- **Giry vs. weak-topology Borel** ("W2"): the coercion
  `ProbabilityMeasure Ω → Measure Ω` is measurable from the Borel σ-algebra
  of the weak topology to the Giry σ-algebra, so measure-valued parameters
  live on a Polish space; plus a **Giry-valued equalizer** lemma: the
  agreement set of two measurable probability-valued families is measurable.

---

## 2. Theorem inventory

All names below are audited in
[`BicausalOT/AxiomsAudit.lean`](BicausalOT/AxiomsAudit.lean) (32 entries).
"BS" = Bertsekas & Shreve, *Stochastic Optimal Control: The Discrete Time
Case*; "Kechris" = Kechris, *Classical Descriptive Set Theory* (GTM 156).
Files are under `BicausalOT/`; DST = `BicausalOT/DescriptiveSetTheory/`.

### Bicausal optimal transport, T = 1

| Lean name | Statement | Reference | File |
|---|---|---|---|
| `kernel_decomp_implies_bicausal` | kernel decomposition `(γ₀, γ₁)` with `γ₀ ∈ Π(μ₀,ν₀)`, `γ₁(z₀) ∈ Γ(z₀)` a.e. ⟹ `π` bicausal | — | `Proposition1.lean` |
| `bicausal_implies_decomp` | converse: a bicausal `π` admits such a decomposition | — | `Proposition1.lean` |
| `V₀_le_cost_pointwise` | `V₀(z₀) ≤ c₀(z₀) + ∫⁻ c₁(z₀,·) dγ` for every `γ ∈ Γ(z₀)` | — | `LowerBound.lean` |
| `bellman_lower_bound` | `∫⁻ V₀ dγ₀ ≤ totalCost(γ₀, γ₁)` for a.e.-feasible `γ₁` | — | `LowerBound.lean` |
| `eps_optimal_element` | in `[0,∞]`: `S` nonempty, `ε > 0` ⟹ `∃ a ∈ S, f a ≤ inf_S f + ε` | — | `UpperBound.lean` |
| `eps_optimal_selection` | pointwise ε-optimal selector `z₀ ↦ γ₁(z₀)` (choice; no measurability claimed) | — | DST `JankovVonNeumann.lean` |
| `eps_optimal_kernel_bound` | ε-optimal transition family for the inner problem | — | `UpperBound.lean` |
| `totalCost_le_V₀_plus_eps` | `totalCost(γ₀, γ₁^ε) ≤ ∫⁻ (V₀ + ε) dγ₀` | — | `UpperBound.lean` |
| `bellman_value_geq` | "≥" half of the value representation | — | `ValueRepresentation.lean` |
| `bellman_value_leq` | "≤" half of the value representation | — | `ValueRepresentation.lean` |
| **`bellman_value_eq`** | **T = 1 Bellman value representation (main theorem)** | — | `ValueRepresentation.lean` |
| `optimal_kernel_exists_pointwise` | a minimizer of `γ ↦ ∫⁻ c₁ dγ` on compact `Γ(z₀)` exists for an l.s.c. objective | — | `Existence.lean` |

### Multi-period Bellman recursion, general T

| Lean name | Statement | Reference | File |
|---|---|---|---|
| `MultiPeriod.VGo_le_costGo` | `VGo k t h ≤ costGo k t h` for every feasible strategy | — | `MultiPeriod.lean` |
| `MultiPeriod.exists_eps_strategy` | ε-optimal strategy at the time-consistent depth `T − t − 1`, fixed horizon `T` | — | `MultiPeriod.lean` |
| `MultiPeriod.costGo_le_VGo_add` | `costGo k t h ≤ VGo k t h + k·ε` for the ε-optimal strategy (`t + k = T`) | — | `MultiPeriod.lean` |
| **`MultiPeriod.bellman_value_eq_multi`** | **T-period Bellman value representation (main theorem)** | — | `MultiPeriod.lean` |

### Descriptive set theory

| Lean name | Statement | Reference | File |
|---|---|---|---|
| `jankov_von_neumann` | analytic `P ⊆ X × Y` has a σ(Σ¹₁)-measurable uniformization | Kechris Thm. 18.1 | DST `Tree.lean` |
| `LowerSemicontinuous.isLowerSemianalytic` | l.s.c. ⟹ lower semianalytic | BS Def. 7.21, Lem. 7.30 | DST `LowerSemianalytic.lean` |
| `IsLowerSemianalytic.iInf_fiber` | fiberwise infimum of an l.s.a. function over an analytic set is l.s.a. | BS Prop. 7.47 | DST `LowerSemianalytic.lean` |
| `Continuous.analyticallyMeasurable` | continuous maps from Polish spaces are σ(Σ¹₁)-measurable | BS Defs. 7.19–7.20 | DST `AnalyticSigmaAlgebra.lean` |
| `MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact` | Choquet capacitability: `μ(A) = ⨆ {μ(K) : K ⊆ A compact}` for finite Borel `μ` | Kechris Thm. 30.13; BS Prop. 7.42 | DST `Capacitability.lean` |
| `MeasureTheory.AnalyticSet.nullMeasurableSet` | analytic sets are universally (null-)measurable | BS Prop. 7.42 (Lusin) | DST `Capacitability.lean` |
| `MeasureTheory.AnalyticSet.kernel_section_gt` | `{x : c < κ x (A_x)}` is analytic (kernel sections are upper semianalytic) | BS Prop. 7.46 | DST `Capacitability.lean` |
| `lintegral_lowerSemianalytic` | `x ↦ ∫⁻ y, f(x,y) ∂(κ x)` is l.s.a. for l.s.a. `f`, Borel-measurable Markov `κ` | BS Prop. 7.48 | DST `KernelIntegral.lean` |

### The space of probability measures on a Polish space

| Lean name | Statement | Reference | File |
|---|---|---|---|
| `isTightMeasureSet_of_cauchySeq` | a Lévy–Prokhorov Cauchy sequence of probability measures is uniformly tight | classical (Prokhorov theory) | DST `ProbabilityMeasurePolish.lean` |
| `exists_diracMix_levyProkhorovDist_le` | natural-weight Dirac mixtures over a dense sequence are `3ε`-dense in LP distance | classical | DST `ProbabilityMeasurePolish.lean` |
| **`ProbabilityMeasure.instPolishSpace`** | **`P(Ω)` with the topology of weak convergence is Polish, for `Ω` Polish** | classical; **not in Mathlib** | DST `ProbabilityMeasurePolish.lean` |
| `probabilityMeasure_continuous_lintegral` | `γ ↦ ∫⁻ f dγ` is weakly continuous for bounded continuous `f ≥ 0` | portmanteau | DST `ProbabilityMeasurePolish.lean` |
| `probabilityMeasure_borel_measurable_apply` | `γ ↦ γ(B)` is Borel(weak)-measurable for every Borel `B` | — | DST `ProbabilityMeasurePolish.lean` |
| `probabilityMeasure_borel_measurable_toMeasure` | "W2": the Giry σ-algebra is ⊆ the Borel σ-algebra of the weak topology | — | DST `ProbabilityMeasurePolish.lean` |
| `countable_generatePiSystem` | the π-system generated by a countable family is countable | — | DST `ProbabilityMeasurePolish.lean` |
| `measurableSet_eq_measure` | Giry-valued equalizer: `{a : F a = G a}` is measurable for measurable probability-valued `F, G` | — | DST `ProbabilityMeasurePolish.lean` |

Also proved en route (audited transitively through the entries above):
the `CompleteSpace`, `SeparableSpace`, `SecondCountableTopology`, and
`PolishSpace` instances for `LevyProkhorov (ProbabilityMeasure Ω)`;
`MultiPeriod.Feas.measure_univ` and `MultiPeriod.VGo_le_pointwise`;
binary closure properties of analytic sets (`AnalyticSet.inter'`,
`AnalyticSet.union'`, `AnalyticSet.preimage_of_continuous`) and a
null-measurable Fubini identity for analytic sets (`AnalyticSet.prod_apply`)
in `KernelIntegral.lean`.

---

## 3. The verification guarantee

**Claim: 0 `sorry`, 0 user-declared axioms, project-wide.** This is
machine-checked, not asserted:

- [`BicausalOT/AxiomsAudit.lean`](BicausalOT/AxiomsAudit.lean) runs
  `#print axioms` on all 32 top-level results. This command makes the Lean
  *kernel* traverse the entire dependency graph of each theorem — every
  lemma, every instance, all the way down through Mathlib — and report every
  axiom the proof ultimately rests on. The output for every entry is a
  subset of

  ```
  [propext, Classical.choice, Quot.sound]
  ```

  Lean 4's three foundational axioms (propositional extensionality, choice,
  quotient soundness) — the classical base on which all of Mathlib is built.
  Nothing else.
- Any `sorry` anywhere in a dependency introduces the pseudo-axiom
  `sorryAx`, which `#print axioms` would list; any user-declared `axiom`
  would likewise appear by name. Neither occurs.
- The build completes with **0 errors and 0 warnings** (a `sorry` would also
  surface as a build warning).

### Reproducing the verification

The build is fully pinned: the Lean toolchain by
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.29.0-rc8`) and every
dependency, including Mathlib, by [`lake-manifest.json`](lake-manifest.json)
(Mathlib rev `00fca21215c51e01d2d90adc3b3d273de909050b`).

```bash
# 1. Install elan, the Lean toolchain manager
#    (https://github.com/leanprover/elan); it picks up the pinned
#    toolchain automatically.

# 2. From the repository root:
cd BicausalOT
lake exe cache get    # fetch prebuilt Mathlib binaries (otherwise Mathlib
                      # compiles from source, which takes hours)
lake build            # compiles the project AND runs the axiom audit
```

`lake build` elaborates `AxiomsAudit.lean` as part of the build, so the
`#print axioms` reports appear in the build log as `info:` lines of the form

```
'MultiPeriod.bellman_value_eq_multi' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

To re-run the audit alone (writes nothing; safe to run concurrently with an
open editor):

```bash
lake env lean BicausalOT/AxiomsAudit.lean
```

---

## 4. Repository layout

| File | Lines | Contents |
|---|---:|---|
| `BicausalOT.lean` | 4 | library root: imports `Basic` + `AxiomsAudit` |
| `BicausalOT/Basic.lean` | 15 | re-exports every module |
| `BicausalOT/Defs.lean` | 54 | `CouplingSet₀`, `FeasibleSet₀`, `KernelDecomp`, `IsBicausal₂`, `V₀`, `totalCost` |
| `BicausalOT/Proposition1.lean` | 35 | bicausal ⟺ kernel decomposition |
| `BicausalOT/LowerBound.lean` | 34 | Step 2: `∫⁻ V₀ ≤ totalCost` |
| `BicausalOT/UpperBound.lean` | 67 | Step 3: ε-optimal construction |
| `BicausalOT/ValueRepresentation.lean` | 112 | Step 4: **`bellman_value_eq`** (T = 1 main theorem) |
| `BicausalOT/Existence.lean` | 34 | Step 5: optimal one-step plan exists (compactness + l.s.c.) |
| `BicausalOT/MultiPeriod.lean` | 253 | histories, strategies, `costGo`/`VGo`, **`bellman_value_eq_multi`** (general T) |
| `BicausalOT/AxiomsAudit.lean` | 64 | `#print axioms` for all 32 audited results |
| `BicausalOT/BicausalOT.lean` | 32 | legacy T = 1 module index (not imported by the root) |
| `BicausalOT/DescriptiveSetTheory/AnalyticSet.lean` | 20 | re-export of Mathlib's analytic sets |
| `BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean` | 95 | the σ-algebra σ(Σ¹₁); analytically measurable functions |
| `BicausalOT/DescriptiveSetTheory/LowerSemianalytic.lean` | 76 | lower semianalytic functions; BS Prop. 7.47 |
| `BicausalOT/DescriptiveSetTheory/Tree.lean` | 314 | leftmost-branch selector; **Jankov–von Neumann** (Kechris 18.1) |
| `BicausalOT/DescriptiveSetTheory/JankovVonNeumann.lean` | 49 | pointwise ε-optimal selection |
| `BicausalOT/DescriptiveSetTheory/Capacitability.lean` | 601 | **Choquet capacitability**; universal measurability; kernel sections |
| `BicausalOT/DescriptiveSetTheory/KernelIntegral.lean` | 468 | **BS Prop. 7.48**: kernel integrals of l.s.a. functions |
| `BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean` | 790 | **`P(Ω)` Polish**: LP completeness + separability; W2; Giry equalizer |
| `BLUEPRINT.md` | — | campaign plan, informal proofs, battle log |
| **Total (Lean)** | **3117** | |

---

## 5. Relation to Mathlib

This project deliberately builds on — and gratefully acknowledges — what
Mathlib already provides:

- **Analytic sets**: the definition, `MeasurableSet.analyticSet`, closure
  under countable unions/intersections and continuous images, and Lusin
  separation (`Mathlib.MeasureTheory.Constructions.Polish.Basic`).
- **The Lévy–Prokhorov metric** on `ProbabilityMeasure Ω` and its
  identification with the topology of weak convergence on separable metric
  spaces (`LevyProkhorov.probabilityMeasureHomeomorph`).
- **Prokhorov's theorem** (`isCompact_closure_of_isTightMeasureSet`) and the
  `IsTightMeasureSet` API.
- Portmanteau lemmas, `HasOuterApproxClosed`, the Giry-monad measurability
  API, and the general measure-theory and integration library.

What is *new here* relative to the pinned Mathlib revision: Choquet
capacitability and universal measurability of analytic sets, upper
semianalyticity of kernel sections, BS 7.48 kernel integration, the analytic
σ-algebra σ(Σ¹₁) and Jankov–von Neumann uniformization, lower semianalytic
functions and BS 7.47, **completeness and separability of the Lévy–Prokhorov
metric** (hence `PolishSpace (ProbabilityMeasure Ω)`), the Giry ⊆ Borel(weak)
comparison, and the Giry-valued equalizer — as well as the bicausal-OT
results themselves.

## 6. References

- D. P. Bertsekas, S. E. Shreve, *Stochastic Optimal Control: The Discrete
  Time Case*, Academic Press, 1978 — Ch. 7 (Borel spaces, analytic sets,
  semianalytic functions, measurable selection).
- A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156, Springer,
  1995 — Thm. 18.1 (Jankov–von Neumann), Thm. 30.13 (capacitability).
- J. Backhoff-Veraguas, M. Beiglböck, Y. Lin, A. Zalashko, *Causal transport
  in discrete time and applications*, SIAM J. Optim. 27(4), 2017 —
  background on (bi)causal transport and its dynamic-programming principle.

[`BLUEPRINT.md`](BLUEPRINT.md) documents the full campaign: design
decisions, informal proofs of every lemma, the walls that were scouted and
brought down (W1: `P(Ω)` Polish; W2: Giry vs. weak Borel), and an
append-only battle log.
