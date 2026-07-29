# FRONT E6 — Mathlib upstreaming battle plan (BicausalOT DST arsenal) — v2

Recon dates 2026-07-07 (v1) and 2026-07-10 (v2 re-audit). Pinned Mathlib rev
`00fca21215c51e01d2d90adc3b3d273de909050b` (master 2026-03-29, toolchain v4.29.0-rc8).
Source files audited: `BicausalOT/DescriptiveSetTheory/Capacitability.lean` (601 L),
`KernelIntegral.lean` (468 L), `ProbabilityMeasurePolish.lean` (790 L — now includes the
Giry-valued equalizer section integrated 2026-07-07), `LowerSemianalytic.lean` (76 L).

**v2 changelog (corrections to the 2026-07-07 draft):**
1. **v1's §1.2 claim "no `MeasurableSpace` instance at all on `ProbabilityMeasure`" is WRONG.**
   The pin has `instance : MeasurableSpace (ProbabilityMeasure Ω)` = the **Giry subtype
   σ-algebra** (`Measure/ProbabilityMeasure.lean:246–248`), plus
   `measurableSet_isProbabilityMeasure` and `measurable_fun_prod` (:261, proved via
   `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`, GiryMonad.lean:95).
   PR3 is redesigned accordingly (§4): the deliverable is a `BorelSpace (ProbabilityMeasure Ω)`
   instance (σ-algebra **equality**), not a choose-your-σ-algebra lemma pack.
2. PR3 gains the **Giry-valued equalizer** material (`measurableSet_eq_measure`,
   `countable_generatePiSystem`) added to the repo after v1 was cached.
3. `probabilityMeasure_continuous_lintegral` folds away completely:
   it is `ProbabilityMeasure.continuous_iff_forall_continuous_lintegral.mp continuous_id f`
   (ProbabilityMeasure.lean:366) — v1 still proposed keeping a wrapper.
4. PR1: added the (free) generality upgrade Polish → metrizable, with proof-audit evidence.
5. PR2b: separability needs **no completeness** (our file already omits it) — hypothesis-
   minimization note added.
6. Prior-art citation added: Isabelle/HOL AFP *The Lévy-Prokhorov Metric* (Hirata, ITP 2024)
   already formalizes LP completeness + Polish-ness — strong precedent for PR2's descriptions.

## 0. Executive summary and dependency graph

```
PR0  (warm-ups: AnalyticSet.inter/union, 2 ENNReal lemmas)            ~60 L
PR1  Choquet capacitability + universal measurability                 ~470 L   ⟂ PR2, PR3
PR1b Parametrized capacitability (kernel superlevel sections)         ~170 L   after PR1
PR2a LP-Cauchy ⇒ tight + CompleteSpace (LevyProkhorov (P Ω))          ~320 L   ⟂ PR1, PR3
PR2b Dirac-mixture density + Separable/SecondCountable/PolishSpace    ~350 L   after PR2a
PR3  BorelSpace (ProbabilityMeasure Ω): Giry = Borel(weak) + equalizer ~260 L  core ⟂ all;
                                                                       StandardBorel needs PR2b
PR4  LowerSemianalytic + BS 7.47 + BS 7.48 (optional, Zulip RFC first) ~600 L  after PR1b
```

PR1, PR2a, PR3-core are mutually independent — submit in parallel. PR0 is optional but
shrinks PR1/PR4 diffs and builds reviewer goodwill.

---

## 1. Ground-truth recon

### 1.1 What Mathlib HAS (pinned rev; all verified by direct read/grep)

- `MeasureTheory.AnalyticSet` (irreducible def), `.image_of_continuous`, `.iUnion`,
  `.iInter` (`[Nonempty ι] [Countable ι] [T2Space α]`), **`.preimage`** (continuous preimage,
  Polish domain, T2 codomain — `Constructions/Polish/Basic.lean:359`), `.measurablySeparable`,
  `MeasurableSet.analyticSet`, `StandardBorelSpace` (same file, :80).
  ⇒ our `AnalyticSet.preimage_of_continuous` (KernelIntegral.lean:53) is a **duplicate of
  Mathlib's `AnalyticSet.preimage`** — drop it from every PR and rewrite call sites.
- Inner regularity: `Measure.InnerRegularWRT` (predicate-parametrized), classes
  `Measure.InnerRegular` / `InnerRegularCompactLTTop`; naming precedents
  `MeasurableSet.measure_eq_iSup_isCompact`, `MeasurableSet.exists_lt_isCompact` (:720),
  `IsOpen.exists_lt_isCompact`; Polish-space instances
  `instInnerRegularOfIsCompletelyPseudoMetrizableSpace`,
  `instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace`
  (RegularityCompacts.lean:177, 190) — **for measurable sets only**.
- LP metric (`Measure/LevyProkhorovMetric.lean`, Kytölä): edist/dist, pseudo-metric and (on
  Borel spaces) metric instances, `levyProkhorovDist_le_of_forall_le`,
  `left/right_measure_le_of_levyProkhorovEDist_lt`,
  `SeparableSpace.exists_measurable_partition_diam_le` (:551),
  `eq_convergenceInDistribution`, `probabilityMeasureHomeomorph` (:694; section variables
  `[PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] [SeparableSpace Ω]`),
  `PseudoMetrizableSpace`/`MetrizableSpace (ProbabilityMeasure X)` instances. Deprecation wave
  dated 2025-10-28 in this file — expect name churn on rebase.
- Prokhorov (`Measure/Prokhorov.lean`, Gouëzel 2025): `isCompact_closure_of_isTightMeasureSet`
  (section variables `[T2Space E] [BorelSpace E]`), P(compact) compact; implementation note
  explicitly says "We do not assume second-countability or metrizability" — a *deliberate*
  design constraint on that file.
- `Measure/Tight.lean`: `IsTightMeasureSet`,
  `isTightMeasureSet_iff_exists_isCompact_measure_compl_le`, `isTightMeasureSet_singleton`.
- Giry side (`Measure/GiryMonad.lean`): `Measure.measurable_coe`, `measurable_of_measurable_coe`,
  `measurable_measure`, `measurable_map`, `measurable_lintegral`, and
  **`Measurable.measure_of_isPiSystem` / `.measure_of_isPiSystem_of_isProbabilityMeasure`**
  (:80, :95) — use these in PR3's assembly.
- **`instance : MeasurableSpace (ProbabilityMeasure Ω)`** — Giry subtype σ-algebra
  (`Measure/ProbabilityMeasure.lean:246–248`), plus `measurableSet_isProbabilityMeasure`,
  `measurable_fun_prod`, `tendsto_iff_forall_lintegral_tendsto` (:335),
  `continuous_iff_forall_continuous_lintegral` (:366). *(v1 missed all of this.)*
- `Measure/DiracProba.lean` (Kytölä 2024): `diracProba`, `isEmbedding_diracProba` — directly
  relevant to PR2b's Dirac mixtures.
- `HasOuterApproxClosed` (typeclass, topological generality) + `IsClosed.apprSeq` +
  `HasOuterApproxClosed.tendsto_lintegral_apprSeq` — exactly the tools our W2 proof uses.
- `MeasurableSpace.CountablyGenerated` class (`MeasurableSpace/CountablyGenerated.lean:55`) —
  the right generality for PR3's equalizer lemma.

### 1.2 What Mathlib LACKS (our contributions; re-verified 2026-07-10)

- **No capacitability**, no universal measurability of analytic sets in any form
  (`universally`/`UniversallyMeasurable`: 0 hits repo-wide; `Souslin` only in doc comments).
- **No** `CompleteSpace`/`SeparableSpace`/`SecondCountableTopology`/`PolishSpace` for
  `LevyProkhorov (ProbabilityMeasure Ω)` or `ProbabilityMeasure Ω`; **no**
  `StandardBorelSpace (ProbabilityMeasure Ω)` (pin grepped; live docs web-checked — see Sources).
- **No `BorelSpace (ProbabilityMeasure Ω)`**: the Giry σ-algebra instance exists but nothing
  relates it to the Borel σ-algebra of the weak topology (either direction).
- No measurable-equalizer lemma for `Measure`-valued maps; no
  `Set.Countable.generatePiSystem`; no `ENNReal.iSup_min_natCast`.
- No `LowerSemianalytic` / semianalytic-function theory; no BS 7.46/7.47-general/7.48.
- No binary `AnalyticSet.inter`/`AnalyticSet.union` (only countable versions).

### 1.3 TODO / roadmap conflicts

- `LevyProkhorovMetric.lean`: **zero** TODO/FIXME/roadmap comments (grepped
  `TODO|FIXME|missing|future|roadmap`, case-insensitive — no hits). Nobody has claimed
  completeness in-file.
- `Prokhorov.lean`: zero TODOs likewise.
- `ProbabilityMeasure.lean:54`: the only nearby TODO — "Probability measures form a convex
  space." Relevant to PR2b (Dirac mixtures ARE convex combinations); cite as
  partially-served motivation.
- Web check of master: `LevyProkhorovMetric.lean` still ends at
  `instMetrizableSpaceProbabilityMeasure`; no completeness/Polish instances in live docs.
  Collision risk: low but nonzero (completeness is the obvious next step after Gouëzel's
  Prokhorov). **Post a Zulip claim message** (`#mathlib4 > Lévy-Prokhorov completeness`)
  before starting PR2a, and cite the Isabelle/HOL AFP formalization (Hirata, ITP 2024) as
  precedent that the full Polish-ness result is upstream-worthy.

### 1.4 Cross-cutting porting requirements (apply to every PR)

1. **Module system**: pinned Mathlib files start with `module`, use `public import`, and
   `@[expose] public section`. All our files use classic headers — mechanical rewrite.
2. **`open scoped Classical` is banned** (used in all three of our files). Replace with
   `classical` tactic in the few proofs needing decidability (`capAux`'s recursion,
   `diracMix`'s `if`, `Finset.filter`), or `open Classical in` on single declarations.
3. **`omit` is disliked** — our files use it ~12×. Restructure into sections with minimal
   `variable` blocks.
4. Copyright header + `Authors:` line per file; module docstring with `# Title`,
   `## Main results`, `## References`, `## Tags`; 100-char lines; `lake exe mk_all`.
5. `docs/references.bib`: `kechris1995` exists; **add `bertsekasShreve1978`**
   (*Stochastic Optimal Control: The Discrete-Time Case*) in PR1.
6. Doc-comments on every public declaration, citing `[kechris1995]` Thm 30.13 /
   `[bertsekasShreve1978]` Props 7.42/7.46/7.47/7.48 inline.

---

## 2. PR1 — Choquet capacitability + universal measurability

**Target file (new)**: `Mathlib/MeasureTheory/Constructions/Polish/Capacitability.lean`.
Rationale: `AnalyticSet` and its measure-theoretic upgrades live under
`Constructions/Polish/`. Second choice: `Mathlib/MeasureTheory/Measure/AnalyticRegularity.lean`
next to `RegularityCompacts.lean` (defensible: the headline IS an inner-regularity statement);
offer both in the PR description, let maintainers pick. Imports:
`Constructions.Polish.Basic`, `Topology.MetricSpace.PiNat`, `Measure.Regular`
(for `InnerRegularWRT`), `Tactic.Finiteness`.

### 2.1 Content and naming (old → new)

Public API (4–5 declarations; everything else folds away):

| Project name | Proposed Mathlib name | Notes |
|---|---|---|
| — (new headline) | `MeasureTheory.innerRegularWRT_isCompact_analyticSet (μ) [IsFiniteMeasure μ] : μ.InnerRegularWRT IsCompact AnalyticSet` | **Primary statement** — the Mathlib-idiomatic phrasing; name mirrors `innerRegularWRT_isCompact_isClosed_measurableSet_of_finite` (RegularityCompacts.lean:205). Answers the inner-regularity-integration question head-on (§2.3.1). |
| `AnalyticSet.measure_eq_iSup_isCompact` | unchanged | Derive via `InnerRegularWRT.measure_eq_iSup`; name already matches `MeasurableSet.measure_eq_iSup_isCompact` exactly. |
| — (new corollary) | `MeasureTheory.AnalyticSet.exists_lt_isCompact : AnalyticSet A → r < μ A → ∃ K ⊆ A, IsCompact K ∧ r < μ K` | Mirrors `MeasurableSet.exists_lt_isCompact` (Regular.lean:720). (The tasked name `exists_isCompact_measure_lt` loses to this established word order.) |
| `AnalyticSet.nullMeasurableSet` | unchanged | Convention-perfect (cf. `MeasurableSet.nullMeasurableSet`). Docstring: "analytic sets are universally measurable (Lusin; BS 7.42)". |
| `AnalyticSet.prod_apply` (from KernelIntegral.lean:138) | unchanged, **moved into PR1** | Null-measurable Fubini `μ.prod ν S = ∫⁻ v, ν (Prod.mk v ⁻¹' S) ∂μ` for analytic `S`; mirrors `Measure.prod_apply`; needs only `nullMeasurableSet` — standalone valuable, advertise. |

Private/folded scaffolding — **all `cap*` prefixes go**; every Part I–V declaration becomes
`private` (used only in-file), EXCEPT the abstract recursion engine which PR1b reuses:

- `capBelow` → delete: it **is** `Set.Iic β` under the `Pi` order (`Pi.le_def`); keep one
  private `isCompact_Iic : IsCompact (Set.Iic β)` for `β : ℕ → ℕ` (or offer a general
  `Pi.isCompact_Iic` — cheap, more useful). `capBelowN`, `capTrunc`, `capSeqs` (+8
  congr/finiteness lemmas) → private (`boundedUpTo`, `truncate`, `prefixReps`; reviewers
  don't bikeshed privates).
- `capScheme`, `capW`, `capR`, `capBranch`, `capKernel` → `souslinScheme`, `souslinApprox`,
  `souslinBounded`, `souslinBranch`, `souslinKernel` under a
  `namespace MeasureTheory.AnalyticSet.Souslin` — **public-but-internal** (docstring:
  "engine for parametrized capacitability, see `AnalyticSet.kernel_section_gt`"), because
  PR1b's statements quantify over `capW`/`cap_exists_bound`. If maintainers prefer, demote
  to private and let PR1b re-open the file (same-file append makes this moot).
- `iInter_capW_subset` (core topological lemma) → private
  `iInter_souslinApprox_subset_image`, keep the long docstring.
- `capKernel_eq_range` → `Souslin.kernel_eq_range`.
- `cap_exists_ext`, `capAux`, `capBound`, `capAux_eq` → private; `cap_exists_bound` →
  `Souslin.exists_bound` (semi-internal, PR1b hook). Keep the abstract
  monotone-sup-continuous functional `m` formulation — costs nothing, and is the hook for a
  future Kechris-30.13 abstract-capacity PR (implementation note, not a TODO).
- `rw [AnalyticSet] at hA` (lines 378, 559): with the irreducible def use `AnalyticSet_def`
  (the `_def` lemma exists; our proofs need the raw Baire-space representation, not
  `analyticSet_iff_exists_polishSpace_range`).

### 2.2 Generality decision (reviewers' first question)

Our statements assume `[PolishSpace X] [BorelSpace X]`. Proof audit shows this is overkill:
- `iInter_capW_subset` uses `upgradeIsCompletelyMetrizable` **only to obtain a metric**;
  completeness is never used (only `Metric.mem_closure_iff`, `dist` estimates,
  `tendsto_nhds_unique` = T2). Any compatible metric works: `[MetrizableSpace X]` suffices
  (`letI := metrizableSpaceMetric X`).
- The measure side needs closed ⇒ measurable (`OpensMeasurableSpace X`) and
  `Directed.measure_iInter` (finite measure). `BorelSpace` is never needed.
- So the honest hypotheses are `[TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]`, `μ` finite — strictly containing the Polish/Borel case
  (analytic sets are defined for arbitrary topological spaces in Mathlib, so nothing breaks).
  **Recommend shipping this generality up front**; fall back to Polish only if elaboration
  friction appears. Note the contrast in the module doc: for *measurable* sets Mathlib's
  inner regularity (RegularityCompacts) needs completeness; for *analytic* sets the
  representation `A = π '' ℕᴺ` supplies the compactness instead.

### 2.3 Likely reviewer requests (prepare answers in the PR description)

1. **"State it as `InnerRegularWRT`"** — pre-empted: it IS the primary statement. Note
   `AnalyticSet` is not a σ-algebra, so the `Measure.InnerRegular` *typeclass* cannot absorb
   this; `InnerRegularWRT IsCompact AnalyticSet` is the correct interface, and the existing
   Polish instances for measurable sets become corollary-cousins, not conflicts.
2. **Finite vs σ-finite vs arbitrary μ.** `IsFiniteMeasure` is used in the
   `Directed.measure_iInter` endgame (`⟨0, measure_ne_top μ _⟩`) — a local `μ A ≠ ∞`
   hypothesis does NOT suffice (the decreasing `capW` sets need finite measure, not `A`).
   σ-finite `nullMeasurableSet` is an easy corollary (decompose into finite pieces,
   intersect Borel hulls, ~25 lines) — offer if requested, don't pre-ship.
3. **"Generalize to abstract Choquet capacities (Kechris 30.13)"** — answer: Part V is
   already abstract in `m`; what is measure-specific is only the decreasing-closed-sets
   endgame (needs ↓-continuity, which capacities only have on compacts — a real design
   decision). Deliberately out of scope; module-doc note. Keeps the PR reviewable.
4. Style: `open scoped Classical` removal, `omit` removal, `Continuous.prodMk` (already new
   name in our code ✓), `by finiteness` (available ✓).

### 2.4 Diff size

Parts I–VI ≈ 455 source lines → ~430 after `Set.Iic` folding + ~60 lines header/docstrings
⇒ **~470–490 lines, one new file** + `references.bib` + `Mathlib.lean`. Above the comfy
size but a coherent unit; flag the split option in the description, don't pre-split.

### 2.5 PR1b — parametrized capacitability (Part VII, follow-up)

Append to the same file (preferred; avoids the private/public dance) or new
`Constructions/Polish/CapacitabilityKernel.lean`. Extra import:
`Probability.Kernel.MeasurableLIntegral` (`Kernel.measurable_kernel_prodMk_left`).
Content: `cap_kernel_exists_bound`, `cap_kernel_le_of_bound`, `capPad`,
`cap_measurable_layer` → all private; public:

- `AnalyticSet.kernel_section_gt` →
  **`MeasureTheory.AnalyticSet.analyticSet_setOf_lt_kernel_prodMk`** (conclusion-describing:
  `AnalyticSet {x | c < κ x (Prod.mk x ⁻¹' A)}`), docstring: "for a finite Borel kernel,
  `x ↦ κ x (A_x)` is upper semianalytic on its superlevel sets (BS 7.46)". Alternative:
  `Kernel.analyticSet_superlevel_section`.

Here Polish X IS required (`MeasurableSet.analyticSet` on `X × ℕᴺ`). ~170 lines.
Expected question: `IsFiniteKernel` vs `IsSFiniteKernel` — direction (b)
(`cap_kernel_le_of_bound`) genuinely needs finiteness (continuity from above); the layer
lemma already only needs s-finite. Keep `IsFiniteKernel` public.

---

## 3. PR2 — LP completeness, separability, `PolishSpace (ProbabilityMeasure Ω)`

**Target**: one **new file** `Mathlib/MeasureTheory/Measure/LevyProkhorovComplete.lean`
(alt name `ProbabilityMeasurePolish.lean`; prefer `LevyProkhorovComplete` — the organizing
theorem is completeness, Polish-ness is the final corollary). It CANNOT be an extension of
`LevyProkhorovMetric.lean`: the proof imports `Measure/Prokhorov.lean` (Riesz–Markov chain)
and `Measure/Tight.lean` — unacceptable import weight on the metric file; and
`Prokhorov.lean` deliberately avoids metrizability (its implementation note), so the
material cannot live there either. Imports: `LevyProkhorovMetric`, `Tight`, `Prokhorov`,
`DiracProba` (PR2b). Split at the natural seam:

### 3.1 PR2a — Cauchy ⇒ tight, and completeness (~320 lines)

| Project name | Proposed Mathlib name | Notes |
|---|---|---|
| `exists_range_measure_ball_compl_lt` | merge — see note (i) | private candidate |
| `cauchySeq_exists_finset_measure_ball_compl_le` | `MeasureTheory.LevyProkhorov.exists_finset_measure_compl_iUnion_ball_le` | the quantitative uniform-tightness layer; keep public (reusable estimate) |
| `isTightMeasureSet_of_cauchySeq` | `MeasureTheory.isTightMeasureSet_range_toMeasure_of_cauchySeq`, restating the set as `Set.range fun n ↦ (u n).toMeasure` | **standalone valuable** — advertise: "LP-Cauchy sequences of probability measures on a Polish space are uniformly tight" |
| `instance : CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω))` | instance (auto-named) | the prize; hypotheses `[MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]` |

Note (i): `exists_range_measure_ball_compl_lt` and PR2b's
`exists_measure_compl_partial_iUnion_lt` are the same lemma ("a finite measure exhausts a
countable (null-)measurable cover: some finite head has complement-mass < ε"). Merge into
ONE general lemma — proposed `MeasureTheory.exists_measure_compl_biUnion_finsetRange_lt` —
in this file (or offered to `Measure/MeasureSpace.lean`). Reviewers will spot the
duplication otherwise; both call sites instantiate with balls / partition cells.

Likely requests:
1. **PseudoMetric generality** — honest answer: no. Prokhorov's compactness runs in a
   `[T2Space E]` section; a pseudometric Ω is not T2. Pseudo-completeness would factor
   through the metric quotient — out of scope, one-line docstring note.
2. **`FiniteMeasure` version** — true (mass is LP-Cauchy-controlled via `B = univ`) but the
   LP↔weak identification (`probabilityMeasureHomeomorph`) is probability-only in Mathlib.
   Answer: probability now; finite-measure analogue is a follow-up gated on a
   `finiteMeasureHomeomorph`. Kytölä (likely reviewer, owns both files) may push here —
   follow-up PR, not blocker.
3. Assembly via `tendsto_nhds_of_cauchySeq_of_subseq` — exists, already used, no issue.

### 3.2 PR2b — Dirac-mixture density, separability, Polish assembly (~350 lines)

| Project name | Proposed Mathlib name | Notes |
|---|---|---|
| `diracMix` | `MeasureTheory.ProbabilityMeasure.diracMix (x₀ : Ω) (x : Fin N → Ω) (a : Fin N → ℕ) : ProbabilityMeasure Ω` — repackage as a bundled `ProbabilityMeasure`, defined via `diracProba` | connects to existing `diracProba` API and the ProbabilityMeasure.lean:54 TODO ("convex space") — cite it |
| `diracMix_sum_ne_zero`, `le_diracMix_apply` | `diracMix_eq_of_sum_ne_zero`, `le_diracMix_apply` | the lower bound is the usable estimate; keep public |
| `exists_measure_compl_partial_iUnion_lt` | merged into PR2a's general lemma | |
| `exists_diracMix_levyProkhorovDist_le` | `ProbabilityMeasure.exists_levyProkhorovDist_diracMix_le` | **standalone valuable** ("ℕ-weighted Dirac mixtures at points of any dense sequence are dense in LP distance") — useful for empirical-measure/approximation arguments. **Tighten `3 * ε` to `ε`** (apply internally at `ε/3`) — reviewers always ask. |
| — (new, recommended) | `ProbabilityMeasure.denseRange_diracMix` | expose the `DenseRange Φ` core instead of burying it; the `SeparableSpace` instance becomes 5 lines |
| `instance : SeparableSpace (LevyProkhorov (ProbabilityMeasure Ω))` | instance | keep the `IsEmpty Ω` branch (totality) |
| `instance : SecondCountableTopology (LevyProkhorov …)` | instance (one line) | |
| `instance : PolishSpace (LevyProkhorov (ProbabilityMeasure Ω))` | instance | |
| `ProbabilityMeasure.instPolishSpace` | `instance : PolishSpace (ProbabilityMeasure X)` for `[TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]` | **the user-facing prize**, via `probabilityMeasureHomeomorph.isClosedEmbedding.polishSpace`; also ship the free `SecondCountableTopology (ProbabilityMeasure X)` |

Hypothesis minimization (new in v2): the density/separability half needs **no completeness**
(our proofs already `omit [CompleteSpace Ω]`) and plausibly runs at
`[PseudoMetricSpace Ω] [SeparableSpace Ω] [OpensMeasurableSpace Ω]` — the exact variable
block of `LevyProkhorovMetric.lean`'s metrization section (`levyProkhorovDist_le_of_forall_le`
lives there; `Measure.dirac_apply_of_mem` needs nothing). Audit while porting and ship the
weakest block that compiles; the Polish assembly instances keep full Polish hypotheses.

Other expected review notes: why ℕ weights with common denominator `m = ⌈N/ε⌉₊ + 1` — add a
comment (avoids all ENNReal subtraction); sigma-type countability of the index — fine via
`Set.range Φ`.

### 3.3 Conflicts / prerequisites

None in-tree (pin + live docs checked). No TODO claims the territory (§1.3). Zulip-announce
before PR2a to avoid racing Kytölä/Gouëzel; cite the Isabelle AFP entry as precedent.

---

## 4. PR3 — `BorelSpace (ProbabilityMeasure Ω)`: Giry σ-algebra = Borel(weak) + equalizer

**Redesigned in v2.** Mathlib already fixes the σ-algebra on `ProbabilityMeasure Ω` — the
Giry subtype σ-algebra (`ProbabilityMeasure.lean:247`). So v1's "state everything against an
explicit `borel (…)`" plan is the wrong shape: with a registered instance, the
Mathlib-idiomatic deliverable is the σ-algebra **equality**, packaged as

```
instance : BorelSpace (ProbabilityMeasure Ω)
```

(`⟨le_antisymm measurableSpace_le_borel borel_le_measurableSpace⟩`-style), after which every
awkward `@Measurable … (borel …)` statement in our repo becomes an ordinary instance-driven
statement, and `Measurable ((↑) : ProbabilityMeasure Ω → Measure Ω)` is just
`measurable_subtype_coe`.

**Target**: new file `Mathlib/MeasureTheory/Measure/ProbabilityMeasureBorel.lean`
(imports `ProbabilityMeasure`, `HasOuterApproxClosed`, `GiryMonad`; + `LevyProkhorovMetric`
for second countability in the reverse inclusion). Alternative: a new section in
`ProbabilityMeasure.lean` — viable but the file is large; maintainers' call. ~260 lines.

Content and naming:

| Project name | Proposed Mathlib name | Notes |
|---|---|---|
| `probabilityMeasure_continuous_lintegral` | **fold away** | = `continuous_iff_forall_continuous_lintegral.mp continuous_id f` (ProbabilityMeasure.lean:366) |
| `probabilityMeasure_borel_measurable_apply_isClosed` | private `measurable_apply_of_isClosed` | outer approximation via `IsClosed.apprSeq` + `measurable_of_tendsto_metrizable`; generality `[HasOuterApproxClosed Ω] [OpensMeasurableSpace Ω]` — topological, matches the Portmanteau library idiom |
| `probabilityMeasure_borel_measurable_apply` | `ProbabilityMeasure.measurable_measure_apply` (stated w.r.t. `borel (ProbabilityMeasure Ω)` locally, or directly as the ≤ half below) | π-λ induction from closed sets (`borel_eq_generateFrom_isClosed`, pseudo-metrizable Ω) |
| `probabilityMeasure_borel_measurable_toMeasure` (W2) | `ProbabilityMeasure.measurableSpace_le_borel : ‹Giry instance› ≤ borel (ProbabilityMeasure Ω)` | assembly via **`Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`** (GiryMonad.lean:95) instead of raw `Measure.measurable_measure` — reviewers know that lemma |
| — (new work, ~60–100 L) | `ProbabilityMeasure.borel_le_measurableSpace` | reverse inclusion: weak topology is second countable (metrizable + separable, PR2b or `instMetrizableSpaceProbabilityMeasure` + separability); subbasic opens are preimages of opens under `γ ↦ γ.testAgainstNN f`, which are Giry-measurable (`Measure.measurable_lintegral` ∘ `measurable_subtype_coe`); conclude by countable-basis generation. Reviewers will NOT accept a one-directional lemma when the iff is in reach — budget for it. |
| — (packaging) | `instance : BorelSpace (ProbabilityMeasure Ω)` for `[PseudoMetricSpace Ω] [SeparableSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]` (weakest block that compiles) | the headline |
| — (corollary, needs PR2b) | `instance : StandardBorelSpace (ProbabilityMeasure X)` for Polish Borel `X` | **the crown jewel** — makes P(X) a legal kernel source/target (disintegration; our Phase-4 use case). Trivial once `PolishSpace` (PR2b) + `BorelSpace` (this PR) exist. Ship in whichever of PR2b/PR3 lands second. |
| `countable_generatePiSystem` (ProbabilityMeasurePolish.lean:739) | `Set.Countable.generatePiSystem` → `Mathlib/MeasureTheory/PiSystem.lean` | dot-notation; pure π-system fact, ~15 lines, belongs in that file |
| `measurableSet_eq_measure` (:759) | `MeasureTheory.measurableSet_eq_measure` | **generalize**: `[PolishSpace W] [BorelSpace W]` → `[MeasurableSpace W] [MeasurableSpace.CountablyGenerated W]` — the proof uses only a countable generating π-system (`Set.Countable.generatePiSystem` of the countable generator) + `ext_of_generate_finite`; keep the probability hypotheses (or `IsFiniteMeasure` + equal total mass). No existing equalizer lemma found in-tree (re-grep `Probability/Kernel/` at PR time). Standalone valuable: "the agreement set of two measurable probability-kernel-like families is measurable". |

Submission strategy: PR3-core (everything except `StandardBorelSpace`) is independent of
PR1/PR2 — submit early; it is small and uncontroversial *given the BorelSpace framing*.
Design risk: a maintainer may prefer `BorelSpace` as a *theorem* (σ-algebra equality) without
instance registration, fearing instance-search cost on a `Subtype` σ-algebra — accept either;
the equality lemma is the content.

---

## 5. PR4 (optional) — `LowerSemianalytic` + BS 7.47 + BS 7.48

**Gate**: introduces a new *concept* (semianalytic functions), not just theorems. Post a
Zulip design RFC first ("DST: lower semianalytic functions and integration along Borel
kernels"). Naming: follow `LowerSemicontinuous` — **drop the `Is` prefix**:
`def LowerSemianalytic (f : X → ℝ≥0∞) : Prop := ∀ c, AnalyticSet {x | f x < c}`.

**Targets** (two new files under `Constructions/Polish/` + kernel file):

- `Mathlib/MeasureTheory/Constructions/Polish/Semianalytic.lean` (~150 L, PR4a):
  - `LowerSemianalytic` def; `LowerSemicontinuous.lowerSemianalytic`;
  - `LowerSemianalytic.analyticSet_le` (sublevel `≤ q`, `q ≠ ∞`);
  - `IsLowerSemianalytic.iInf_fiber` → `LowerSemianalytic.iInf_of_analyticSet` (BS 7.47) —
    clean up the `Fin 2`/`Matrix.cons` intersection hack with PR0's binary `AnalyticSet.inter`;
  - `LowerSemianalytic.analyticSet_epigraph`;
  - codomain-generality risk: reviewers may want `EReal` or order-generic. Position: ℝ≥0∞
    matches `lintegral`; duals/EReal are follow-ups. If review stalls, re-cut with an
    `UpperSemianalytic` dual for ℝ≥0∞ only.
- `Mathlib/Probability/Kernel/LowerSemianalytic.lean` (~450 L, PR4b; needs PR1b + PR4a +
  PR1's `AnalyticSet.prod_apply`):
  - `aemeasurable_of_analytic_sublevels` → `LowerSemianalytic.aemeasurable`
    (universal a.e.-measurability, BS 7.42 corollary — standalone valuable, advertise);
  - `volume_restrict_epigraph_section` → private;
  - `lintegral_lowerSemianalytic` → **`LowerSemianalytic.lintegral_kernel`** (BS 7.48),
    RESTATED with `(κ : Kernel X Y) [IsMarkovKernel κ]` instead of our raw
    `{κ : X → Measure Y} (hκ : Measurable κ) (hκp : …)` triple — the #1 guaranteed reviewer
    request. `IsFiniteKernel` generalization (truncation bound becomes `n * C`): offer as
    follow-up, ship Markov.
  - ENNReal helpers `ennreal_le_iff_forall_lt_add_inv`, `ennreal_iSup_min_natCast` → PR0.

---

## 6. PR0 — warm-up PR (optional, ~60 lines, zero risk)

Into `Constructions/Polish/Basic.lean` and `Data/ENNReal/` (Inv/Order):

1. `AnalyticSet.inter` (binary, `[T2Space α]`) and `AnalyticSet.union` — from our
   `inter'`/`union'` (KernelIntegral.lean:32,41), derived via `iInter`/`iUnion` over `Bool`;
   place beside the countable versions.
2. `ENNReal.iSup_min_natCast : ⨆ n : ℕ, min a n = a` (verified absent).
3. (optional) the `le_iff_forall_lt_add_inv` natCast variant, or inline it at its 3 call sites.
4. Delete-on-port: `AnalyticSet.preimage_of_continuous` (use Mathlib's `AnalyticSet.preimage`).

Cuts ~90 lines from PR4 and starts the review relationship cheaply.

---

## 7. Sequencing, sizes, effort

| Order | PR | Target file | Size | Depends on | Parallel? |
|---|---|---|---|---|---|
| 1 | PR0 warm-ups | Polish/Basic.lean, ENNReal | ~60 L | — | yes |
| 1 | PR3-core BorelSpace P(Ω) + equalizer | Measure/ProbabilityMeasureBorel.lean (new) + PiSystem.lean | ~260 L | — | yes |
| 1 | PR2a LP-Cauchy⇒tight + CompleteSpace | Measure/LevyProkhorovComplete.lean (new) | ~320 L | — | yes |
| 1 | PR1 capacitability + universal msb. + prod_apply | Constructions/Polish/Capacitability.lean (new) | ~470 L | (PR0 nice) | yes |
| 2 | PR2b diracMix density + PolishSpace | same file as PR2a | ~350 L | PR2a | after 2a |
| 2 | PR1b parametrized capacitability | append to Capacitability.lean | ~170 L | PR1 | after 1 |
| 2 | StandardBorelSpace P(X) instance | wherever lands second | ~10 L | PR2b + PR3 | — |
| 3 | PR4a LowerSemianalytic + 7.47 | Constructions/Polish/Semianalytic.lean (new) | ~150 L | PR0, PR1 | Zulip RFC first |
| 3 | PR4b BS 7.48 | Probability/Kernel/LowerSemianalytic.lean (new) | ~450 L | PR1b, PR4a | after 4a |

Common porting overhead: module-system headers, de-`omit`, de-`Classical`,
`references.bib` (`bertsekasShreve1978`), doc polish — budget ~1 compile-fix session per PR
on top of the mechanical copy (proofs are green against this exact rev; only risk is master
drift in lemma names between pin (2026-03-29) and PR branch — rebase early, fix names; watch
the LP file's 2025-10-28 deprecation aliases).

Total: ~2,200 lines across 7–9 PRs. The three independent openers (PR1, PR2a, PR3-core)
cover the campaign's three genuinely missing Mathlib capabilities: capacitability/universal
measurability of analytic sets, LP-completeness/Polish-ness of P(Ω), and the
Giry-vs-weak-Borel bridge; PR2b+PR3 jointly yield `StandardBorelSpace (ProbabilityMeasure X)`
— the single most reusable payoff for downstream probability theory.

---

### Sources (external web checks, 2026-07-10)

- [Mathlib docs: MeasureTheory.Measure.LevyProkhorovMetric](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.html) — no completeness/Polish instances on live master.
- [Mathlib docs: MeasureTheory.Measure.Prokhorov](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Prokhorov.html)
- [mathlib4 GitHub: LevyProkhorovMetric.lean (master)](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean)
- [Mathlib docs: MeasureTheory.Constructions.Polish.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Polish/Basic.html)
- [Isabelle AFP: The Lévy-Prokhorov Metric (Hirata)](https://isa-afp.org/browser_info/current/AFP/Levy_Prokhorov_Metric/outline.pdf) · [ITP 2024 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.21/LIPIcs.ITP.2024.21.pdf) — prior art for PR2.
