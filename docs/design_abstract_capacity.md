# F6 — Abstract Choquet capacitability: recon + design

Front F6 of wf_1997d83e-337 (hypothesis-elimination wave). Recon + plan only, no heavy Lean.
Source file analyzed: `BicausalOT/DescriptiveSetTheory/Capacitability.lean` (green, 601 lines).
All Mathlib API names below were verified by grep against the pinned Mathlib checkout
(`.lake/packages/mathlib`, toolchain v4.29.0-rc8).

**Headline findings**

1. The recursion (Part V) and all scheme combinatorics (Parts I, II, IV) generalize **verbatim** —
   Part V is literally already stated over an abstract monotone functional `m` with
   countable-increasing-sup continuity; nothing to change, not even signatures.
2. The endgame does NOT generalize under the naive axiom "continuity along decreasing sequences of
   compacts" (C3a). The suggested classical fix — intersect with the compact witness,
   `K₀ ∩ W(β,n)` decreasing compacts — **fails honestly**: the recursion lower-bounds
   `φ(W(β,n))` via `capR ⊆ capW`, but `capR π β n ⊄ K₀` (branches are bounded only on the first
   `n` coordinates), so no lower bound on `φ(K₀ ∩ Wₙ)` is available. Worse, **no repair exists**:
   there is a concrete monotone, increasing-continuous, compact-decreasing-continuous functional on
   `ℕ → ℕ` for which capacitability of analytic sets is FALSE (§2.3). (C3a) alone is the wrong axiom.
3. The correct third axiom is **outer regularity on compacts** (C3b):
   `φ K = ⨅ (U ⊇ K open), φ U`. With it the endgame closes via a *strengthened, purely topological*
   core lemma ("uniform open absorption": every open `U ⊇ ⋂ₙ Wₙ` already contains some `Wₙ`),
   proved by the same moving-point subsequence extraction as the existing `iInter_capW_subset`.
   (C3b) + monotonicity implies (C3a) restricted to compacts, so nothing is lost.
4. Payoff beyond aesthetics: the measure instantiation only needs `[μ.OuterRegular]` — **finiteness
   of μ is no longer required**. The current `IsFiniteMeasure` theorem is recovered through the
   Mathlib instance `WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`, and we gain, e.g.,
   inner regularity of Lebesgue measure on analytic sets (μ A = ∞ case included) for free. The
   old `Directed.measure_iInter` endgame genuinely cannot do this (decreasing continuity fails for
   infinite measures), so the abstract route is a strict mathematical strengthening.
5. Recommendation: **worth doing, at low priority for the repo, high value for the Mathlib PR**
   (~200 new lines; details and exact statements in §4).

---

## §1. The abstract framework (Kechris §30, "Capacities")

Kechris, *Classical Descriptive Set Theory*, Chapter 30: 30.A basic concept (Definition 30.1),
30.B examples (30.2: outer measures of finite Borel measures, Newtonian capacity, separation
capacities, ...), 30.C the Choquet Capacitability Theorem (30.13).

*Caveat recorded for honesty:* the book itself could not be fetched this session (the known PDF
mirror refused connections); the axioms below are therefore pinned down mathematically rather than
bibliographically — §2.3 proves that the (C3b) form is the only one under which 30.13 as usually
quoted ("every analytic subset of a Polish space is capacitable") is actually true, and secondary
sources (Cohn, *Measure Theory*, analytic-sets chapter; almostsuremath.com's Choquet post for the
contrasting paving-relative Dellacherie–Meyer form) are consistent with this. Verify exact wording
against the book at PR time.

**Definition (capacity).** Let `X` be a Polish (separable metrizable suffices for the definition)
space. A *capacity* on `X` is `φ : Set X → ℝ≥0∞` such that

- (C1) monotone: `S ⊆ T → φ S ≤ φ T`;
- (C2) continuous along increasing sequences of **arbitrary** sets:
  `Monotone s → φ (⋃ n, s n) = ⨆ n, φ (s n)`;
- (C3b) outer-regular on compacts: `IsCompact K → φ K = ⨅ (U) (_ : K ⊆ U) (_ : IsOpen U), φ U`.

No `φ ∅ = 0`, no subadditivity, no finiteness is needed anywhere below.

**Remark (relation to the "decreasing compacts" form (C3a)).** (C1)+(C3b) imply
`φ (⋂ n, K n) = ⨅ n, φ (K n)` for decreasing compacts `Kₙ` in a T2 space: `≤` is monotonicity;
for `≥`, given open `U ⊇ ⋂ Kₙ`, the compacts `Kₙ \ U` decrease with empty intersection, so some
`Kₙ ⊆ U`, giving `⨅ φ(Kₘ) ≤ φ U`; take the infimum over `U` and rewrite with (C3b).
So the (C3b) axiomatization subsumes the (C3a) one on its domain of validity. The converse fails,
and (C3a) alone does not support the theorem — see §2.3.

**Theorem (Choquet capacitability, Kechris 30.13, measure-free form).** `X` Polish, `φ` a capacity
on `X`, `A ⊆ X` analytic. Then

```
φ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), φ K.
```

The Dellacherie–Meyer tradition (Probabilities and Potential, III) instead keeps (C3a) but relative
to a *paving* ℰ, and proves capacitability only for **ℰ-Souslin** sets (Souslin kernels of schemes
with pieces in ℰ). For the compact paving of a non-σ-compact Polish space this class is strictly
smaller than the analytic sets (e.g. `ℕ^ℕ` itself is not 𝒦-Souslin: any Souslin kernel of compact
pieces is contained in the countable union of its pieces, hence σ-compact). The two traditions are
consistent; only the (C3b)-style axiom yields the clean "all analytic sets" statement we want.

---

## §2. Mapping the existing proof onto the abstract framework

### 2.1 What generalizes verbatim (zero changes)

| Piece | Status |
|---|---|
| Part I (`capBelow`, `capBelowN`, `capSeqs`, `capTrunc`, finiteness, `isCompact_capBelow`) | verbatim — pure combinatorics/topology of `ℕ → ℕ` |
| Part II (`capScheme`, `capW`, antitonicity, congr lemmas, `isClosed_capW`) | verbatim — topology only |
| Part IV (`capBranch`, `capKernel`, `capR`, `capR_subset_capW`, `capKernel_eq_range`) | verbatim |
| **Part V recursion** (`cap_exists_ext`, `capAux`, `capBound`, `capAux_eq`, `cap_exists_bound`) | **verbatim, including signatures** — it is already stated for an abstract `m : Set Z → ℝ≥0∞` with exactly (C1) (`hmono`) and (C2) (`hsup`). Instantiate `m := ⇑φ`. Its conclusion `∀ n, c < m (capW π β n)` is exactly what the abstract endgame consumes. |

Checked in detail: `cap_exists_bound π (⇑φ) φ.mono φ.iUnion_monotone h0` typechecks shape-for-shape
against the current signature (lines 350–362 of Capacitability.lean); the only measure-flavored
inputs it ever received were `measure_mono` and `Monotone.measure_iUnion`, i.e. precisely (C1), (C2).

### 2.2 What must change: the endgame (current Part VI, lines 386–401)

Current measure endgame:

```
μ (⋂ n, capW π β n) = ⨅ n, μ (capW π β n)      -- Directed.measure_iInter, needs:
                                               --   * NullMeasurableSet (closed sets)
                                               --   * finiteness  ⟨0, measure_ne_top μ _⟩
   ≥ c                                          -- recursion
μ (π '' capBelow β) ≥ μ (⋂ n, capW π β n)       -- core lemma iInter_capW_subset + measure_mono
```

This is continuity along a decreasing sequence of **closed non-compact** sets — a property of
finite measures, NOT of abstract capacities (not even of infinite measures: Lebesgue,
`Wₙ = [n, ∞)`). This is the one step that must be re-proved from capacity axioms.

### 2.3 Honest analysis of the classical "intersect with the compact witness" fix — it FAILS

Proposed fix (task brief): `Cₙ := K₀ ∩ W(β,n)` with `K₀ := π '' capBelow β` compact. Indeed:
`Cₙ` are decreasing compacts and, by the core lemma `⋂ₙ Wₙ ⊆ K₀`,
`⋂ₙ Cₙ = K₀ ∩ ⋂ₙ Wₙ = ⋂ₙ Wₙ =: K`. So (C3a) gives `φ K = ⨅ₙ φ (K₀ ∩ Wₙ)` — the *upper* structure
is fine. The problem is the **lower bound**: the recursion delivers `c < φ (capR π β n)` and
`capR π β n ⊆ capW π β n`, hence `c < φ (Wₙ)`; but

- `capR π β n ⊄ K₀`: a branch `capBranch π σ` with `σ ∈ capBelowN β n` is only constrained on its
  first `n` coordinates — the tail of `σ` is unbounded, so `π σ` (and the whole branch) generally
  escapes `π '' capBelow β`. Hence `c < φ (K₀ ∩ Wₙ)` is NOT available, and monotonicity runs the
  wrong way. The chain `φ(K) = ⨅ φ(K₀ ∩ Wₙ) ≤ ⨅ φ(Wₙ)` bounds `φ K` from ABOVE by the quantity we
  control from below. Dead end.

**And no rescue is possible under (C3a) alone — counterexample.** On `X := ℕ^ℕ` define

```
φ S := 0  if S is contained in some σ-compact subset of X,   1 otherwise.
```

- (C1) ✓. (C2) ✓: if every `Sₙ` lies in a σ-compact `Cₙ` then `⋃ Sₙ ⊆ ⋃ Cₙ`, still σ-compact;
  otherwise both sides are 1.
- (C3a) ✓ trivially: every compact is σ-compact, so `φ ≡ 0` on compacts and on decreasing
  intersections of compacts.
- `A := ℕ^ℕ = range id` is analytic. `φ A = 1`: `X` is not σ-compact (a compact `K ⊆ ℕ^ℕ` has all
  coordinate projections finite, hence is pointwise bounded; given `X = ⋃ₙ Kₙ` with bounds `bₙ`,
  the diagonal `x(i) := b_i(i) + 1` escapes every `Kₙ`). But
  `⨆ {φ K : K ⊆ A compact} = 0 ≠ 1 = φ A`. Capacitability fails.
- Consistency check: `φ` violates (C3b) at every nonempty compact `K` — every nonempty open
  `U ⊆ ℕ^ℕ` contains a cylinder `N_s ≅ ℕ^ℕ`, closed in `X` and intrinsically non-σ-compact, so if
  `U ⊆ C` with `C` σ-compact then `N_s = ⋃ (Kₙ ∩ N_s)` would be σ-compact; hence `φ U = 1` while
  `φ K = 0`.

So the design decision is forced: **adopt (C3b) as the third axiom** and replace the endgame, not
patch it.

### 2.4 The correct abstract endgame: uniform open absorption

Strengthen the core lemma from a statement about points of `⋂ₙ Wₙ` to a statement about *sequences
through the `Wₙ`*. Both are proved by the same subsequence-extraction; the existing proof of
`iInter_capW_subset` (lines 180–231) is the special case of a constant sequence.

**Lemma A (subsequence extraction, generalizes `iInter_capW_subset`).**
`Z` Polish (metrizable suffices — the existing proof already uses only
`upgradeIsCompletelyMetrizable` for a `dist`, never completeness), `π` continuous, `β : ℕ → ℕ`,
`y : ℕ → Z` with `y n ∈ capW π β n` for all `n`. Then there are `x ∈ π '' capBelow β` and a strict
mono `φ : ℕ → ℕ` with `y ∘ φ → x`.

*Proof (delta against the existing proof).* For each `n` choose `s n ∈ capSeqs β n` with
`y n ∈ capScheme π (s n) n`, then `τ n ∈ PiNat.cylinder (s n) n` with `dist (y n) (π (τ n)) < 1/(n+1)`
(`Metric.mem_closure_iff`). `τ n` is `β`-bounded on its first `n` coordinates; clip
`ρ n := fun i => min (τ n i) (β i) ∈ capBelow β`; extract `ρ ∘ φ → σ ∈ capBelow β`
(`isCompact_capBelow.tendsto_subseq`). Coordinatewise, `ρ (φ j) i = τ (φ j) i` once `φ j > i`, so
`τ ∘ φ → σ` pointwise, so `π (τ (φ j)) → π σ`, and `dist (y (φ j), π (τ (φ j))) → 0` gives
`y ∘ φ → π σ =: x`. ∎ (Identical skeleton to lines 186–231; the only novelty is that `y` moves.)

**Lemma B (uniform open absorption — the new topological endgame input).**
Same hypotheses; `U` open with `(⋂ n, capW π β n) ⊆ U`. Then `∃ n, capW π β n ⊆ U`.

*Proof.* By contradiction: pick `y n ∈ capW π β n \ U` (if some `Wₙ = ∅` it is trivially `⊆ U`).
Lemma A gives `y ∘ φ → x`. `x ∈ ⋂ₙ Wₙ`: fix `n`; for `φ j ≥ n` (StrictMono ⇒ `φ j ≥ j`),
`y (φ j) ∈ W_{φ j} ⊆ Wₙ` (`capW_antitone`), and `Wₙ` is closed (`isClosed_capW`), so the limit `x`
lies in `Wₙ`. Hence `x ∈ U` open, so `y (φ j) ∈ U` eventually — contradicting `y m ∉ U` for all
`m`. ∎ (~20 lines; note this genuinely uses closedness AND antitonicity of `capW`, both on hand.)

*Aside:* the classical counterexample `Wₙ = {0} ∪ [n,∞) ⊆ ℝ` shows decreasing closed sets do NOT
absorb into opens in general; Lemma B works because the extraction pins every escaping sequence
inside the compact `π '' capBelow β`. This is exactly where "closed-but-not-compact `Wₙ`" gets
repaired — at the topology layer, not the capacity layer.

**Abstract endgame.** Given `c < φ A`, `A = range π` (the `A = ∅` disjunct of `AnalyticSet` is a
2-line separate case: take `K := ∅`): pick `c' ∈ (c, φ A)` (`exists_between`), transport across
`capKernel_eq_range`, run `cap_exists_bound π (⇑φ) φ.mono φ.iUnion_monotone` to get `β` with
`∀ n, c' < φ (capW π β n)`. Set `K := ⋂ n, capW π β n`. Then:

- `K` is closed, `K ⊆ π '' capBelow β` (existing `iInter_capW_subset`, or Lemma A with constant
  sequences after a nonemptiness split), hence compact (`IsCompact.of_isClosed_subset`, verified
  present in Mathlib) and `K ⊆ range π = A`;
- `φ K ≥ c'`: rewrite with (C3b); for every open `U ⊇ K`, Lemma B yields `n` with `Wₙ ⊆ U`, so
  `φ U ≥ φ Wₙ > c'`; conclude `⨅ ≥ c'` (`le_iInf`; the family is nonempty via `U := univ`, and an
  empty `⨅ = ∞` would be harmless anyway);
- `c < c' ≤ φ K ≤ ⨆ (K)(_ : IsCompact K)(_ : K ⊆ A), φ K`, and `le_of_forall_lt` closes the
  nontrivial `≤` direction; the `≥` direction is monotonicity, as now.

No decreasing continuity, no measurability, no finiteness anywhere.

---

## §3. The measure instantiation (recovers and strengthens the current theorem)

`Set.measure_eq_iInf_isOpen (A : Set α) (μ : Measure α) [OuterRegular μ] : μ A = ⨅ (U) (_ : A ⊆ U) (_ : IsOpen U), μ U`
holds in Mathlib for **arbitrary** sets (verified, `Mathlib/MeasureTheory/Measure/Regular.lean:368`),
and `Monotone.measure_iUnion` holds for arbitrary monotone families (verified,
`MeasureSpace.lean:485`; the current file already uses it on non-measurable sets at line 385). So:

```lean
/-- An outer regular measure, viewed as a Choquet capacity. -/
noncomputable def MeasureTheory.Measure.toCapacity {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.OuterRegular] : Capacity X where
  toFun S := μ S
  mono' _ _ h := measure_mono h
  iUnion_monotone' _ hs := hs.measure_iUnion
  isCompact_iInf_isOpen' K _ := K.measure_eq_iInf_isOpen μ   -- compactness not even needed here
```

Note the instantiation needs no `BorelSpace`, no T2, no finiteness — outer regularity for arbitrary
sets does all the work. Then:

```lean
/-- Capacitability for outer regular Borel measures — strictly generalizes the current
`measure_eq_iSup_isCompact` (no finiteness). Covers e.g. Lebesgue measure, including μ A = ∞. -/
theorem MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact_of_outerRegular
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    {A : Set X} (hA : AnalyticSet A) (μ : Measure X) [μ.OuterRegular] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K :=
  μ.toCapacity.analyticSet_eq_iSup_isCompact hA    -- `⇑μ.toCapacity = (μ ·)` is rfl
```

Recovering the existing theorem byte-for-byte: with `[BorelSpace X] [IsFiniteMeasure μ]`, the
instance chain `PolishSpace → IsCompletelyMetrizableSpace → MetrizableSpace →
PseudoMetrizableSpace` (all verified instances, `CompletelyMetrizable.lean:214`,
`Metrizable/Basic.lean:123`) fires
`WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure` (`Regular.lean:1050`), and
`WeaklyRegular extends OuterRegular` (`Regular.lean:324`), so:

```lean
theorem MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact ...  [IsFiniteMeasure μ] ... :=
  hA.measure_eq_iSup_isCompact_of_outerRegular μ   -- statement unchanged; audits unchanged
```

The existing Part VI proof (with `Directed.measure_iInter`) can then either be deleted (replaced by
this 1-liner) or kept; recommend replacing, and keeping `AnalyticSet.nullMeasurableSet` untouched
(it consumes only the sup-statement). Part VII (`kernel_section_gt`) should stay on its direct
measure route: `S ↦ κ x (Prod.mk x ⁻¹' S)` for finite `κ x` *is* a capacity on `X × Y` (outer
regularity of the section functional can be arranged with the open set
`(univ ×ˢ V) ∪ ({x}ᶜ ×ˢ univ)`), but rerouting it through the abstract theorem saves nothing — the
existing 15-line `cap_kernel_le_of_bound` is simpler than the detour. No change there.

---

## §4. Mathlib upstreaming assessment

**Is it worth it? Yes — the abstract version should be the PR's centerpiece.** Reasons:

1. It is the textbook statement (Kechris 30.13). A Mathlib reviewer seeing the measure-only version
   will ask "why not a capacity?"; the recursion is already abstract, so the marginal cost is only
   the two topological lemmas of §2.4 plus a small structure (~200 lines total over the current
   file).
2. It strictly strengthens the measure corollary: `IsFiniteMeasure` → `OuterRegular` (Lebesgue and
   all Radon-type measures included; the `μ A = ∞` case works). Mathlib currently has inner
   regularity machinery only for measurable sets; "analytic sets are inner regular for outer
   regular measures on Polish spaces" is genuinely new there, as is universal measurability of
   analytic sets downstream.
3. Capacities have independent constituencies (potential theory, stochastic processes, optimal
   transport duality à la Beiglböck–Léonard–Schachermayer, which cites exactly Kechris §30).
4. The counterexample of §2.3 is a design argument reviewers will want to see in the module
   docstring: it justifies the (C3b) axiom choice against the more familiar-looking (C3a).

**Exact proposed statements (Lean-like, final names bikesheddable):**

```lean
/-- A **Choquet capacity** on a topological space (Kechris, CDST, 30.1): monotone,
continuous along increasing sequences of arbitrary sets, and outer-regular on compacts.
Neither `φ ∅ = 0` nor subadditivity is assumed. -/
structure MeasureTheory.Capacity (X : Type*) [TopologicalSpace X] where
  toFun : Set X → ℝ≥0∞
  mono' : ∀ ⦃S T : Set X⦄, S ⊆ T → toFun S ≤ toFun T
  iUnion_monotone' : ∀ s : ℕ → Set X, Monotone s → toFun (⋃ n, s n) = ⨆ n, toFun (s n)
  isCompact_iInf_isOpen' : ∀ ⦃K : Set X⦄, IsCompact K →
    toFun K = ⨅ (U : Set X) (_ : K ⊆ U) (_ : IsOpen U), toFun U
-- + DFunLike instance, `ext`, and restating lemmas `Capacity.mono`,
--   `Capacity.iUnion_monotone`, `Capacity.isCompact_iInf_isOpen`.

/-- **Choquet capacitability theorem** (Kechris 30.13): analytic subsets of a Polish space
are capacitable. Measure-free: no `MeasurableSpace` in sight. -/
theorem MeasureTheory.Capacity.analyticSet_eq_iSup_isCompact
    {X : Type*} [TopologicalSpace X] [PolishSpace X] (φ : Capacity X)
    {A : Set X} (hA : AnalyticSet A) :
    φ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), φ K
```

supporting lemmas (topology layer, stated on the existing `capW`):

```lean
theorem capW_exists_tendsto_subseq {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) (β : ℕ → ℕ) {y : ℕ → Z}
    (hy : ∀ n, y n ∈ capW π β n) :
    ∃ x ∈ π '' capBelow β, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 x)

theorem capW_exists_subset_isOpen {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) (β : ℕ → ℕ) {U : Set Z}
    (hU : IsOpen U) (hKU : (⋂ n, capW π β n) ⊆ U) : ∃ n, capW π β n ⊆ U
```

plus `Measure.toCapacity` and `measure_eq_iSup_isCompact_of_outerRegular` as in §3.

**Size estimate.**
- Repo delta: Capacity structure + accessors ~50, Lemma A ~55 (existing 50-line proof with a moving
  point), Lemma B ~20, abstract theorem ~40, `Measure.toCapacity` + outer-regular corollary +
  finite-measure re-derivation ~40 ⇒ **~200 new lines**; net ~150 if `iInter_capW_subset` is
  refactored as a corollary of Lemma A (constant sequence + `tendsto_nhds_unique`) and old Part VI
  is swapped for the 1-liner. New audit entries: `Capacity.analyticSet_eq_iSup_isCompact`,
  `measure_eq_iSup_isCompact_of_outerRegular` (existing audited names keep their statements).
- Mathlib PR: Parts I–V (~360 lines) + the ~200 above + module docs ≈ **600–650 lines**; suggest
  splitting: PR-A "Souslin scheme of a continuous map + uniform open absorption" (pure topology,
  ~380) and PR-B "Choquet capacities and the capacitability theorem + measure corollaries" (~270).
  Defer Part VII (BS 7.46 kernel lemma) to the Bertsekas–Shreve-flavored follow-up PR — it is what
  the E6 PR-plan agent owns; this document only feeds them the abstract-layer recommendation.

**Repo integration plan** (main loop is sole writer): new file
`BicausalOT/DescriptiveSetTheory/CapacityAbstract.lean` importing `Capacitability.lean` — add-only,
does not touch the green file; optionally a later cleanup pass rebases Part VI/`iInter_capW_subset`
onto it. Priority: BELOW Phase-3 integration — nothing in Phases 3–4 depends on F6.

**Lean friction forecast** (all low): `upgradeIsCompletelyMetrizable` `letI` inside Lemma A exactly
as in the current core lemma; `by_contra`/`push_neg` through `¬ ∃ n, Wₙ ⊆ U`; `StrictMono.le_apply`
for `φ j ≥ j`; keep the `⨅ (U) (_ : K ⊆ U) (_ : IsOpen U)` binder order identical to
`Set.measure_eq_iInf_isOpen` so the instantiation is `rfl`-adjacent; `DFunLike` boilerplate copied
from `OuterMeasure`.

---

## §5. Adversarial check record

Standing order was to spawn a sub-agent for the endgame check; **no Agent/Task spawn tool exists in
this sub-session's toolset** (confirmed by two ToolSearch queries), so the check was run as an
explicit in-session attack pass instead. Attacks and outcomes:

1. *Does the recursion secretly use measure properties?* No — re-read Part V; inputs are exactly
   (C1),(C2); `ℝ≥0∞` bookkeeping is `lt_iSup_iff` only. Verbatim reuse confirmed.
2. *Does Lemma A need completeness/second-countability?* No — metric (for `mem_closure_iff`/`dist`)
   + compactness of `capBelow β` + continuity of `π`; same as the existing proof.
3. *Lemma B's limit membership:* needs `capW_antitone` + `isClosed_capW` + `StrictMono.le_apply`;
   all present. Empty-`Wₙ` degenerate case handled (empty set is trivially ⊆ U, contradicting the
   by_contra hypothesis, so in the contradiction branch all `Wₙ` are nonempty).
4. *Circularity check:* `β` is fixed by the recursion before `U` is quantified; `n = n(U)` may
   depend on `U`. No circularity.
5. *The K₀ ∩ Wₙ classical fix:* fails — `capR π β n ⊄ π '' capBelow β` because branch bounds stop
   at coordinate `n` (§2.3). This was the task's suspicion; confirmed.
6. *Could (C3a) still suffice via another route?* No — σ-compact-hull counterexample (§2.3), each
   axiom checked, non-σ-compactness of `ℕ^ℕ` proved by diagonal escape from pointwise bounds, and
   its (C3b)-violation verified for consistency.
7. *(C3b) ⇒ (C3a)-on-compacts remark:* proved via `Kₙ \ U` compact decreasing FIP argument (needs
   T2, available on Polish); direction of both inequalities checked.
8. *Measure instantiation:* `Set.measure_eq_iInf_isOpen` holds for arbitrary sets (grep-verified,
   binder order noted); `Monotone.measure_iUnion` measurability-free (grep-verified);
   `WeaklyRegular extends OuterRegular` and the finite-measure-on-pseudo-metrizable instance
   grep-verified; `PolishSpace → PseudoMetrizableSpace` instance chain grep-verified (no `letI`
   upgrade needed in the corollary).
9. *Infinite-measure sanity:* for `μ A = ∞` the `le_of_forall_lt` scaffolding produces compacts of
   measure `> c` for every `c < ∞`, hence sup `= ∞`; no step assumed `φ A < ∞` (also `exists_between`
   works in `ℝ≥0∞` with `c < ∞`).
10. *Empty analytic set / empty infimum:* `A = ∅` case closes with `K = ∅` without `φ ∅ = 0`;
    the (C3b) infimum family is nonempty (`univ`).

Residual risks: exact wording of Kechris 30.1 unverified against the book (mirror down) — cosmetic,
affects docstring citation only; Mathlib name/style bikeshedding on `Capacity` (structure vs
unbundled hypotheses — recommend bundled + DFunLike, matching `OuterMeasure`/`Content`).
