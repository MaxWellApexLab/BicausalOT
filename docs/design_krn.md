# FRONT E3 — Kuratowski–Ryll-Nardzewski measurable selection: recon + formalization plan

Date: 2026-07-07. Recon target: the pinned Mathlib checkout (`.lake/packages/mathlib`) (v4.29.0-rc8 toolchain).
Re-verified 2026-07-10: all §1–§2 ingredient names/line numbers re-checked by grep against the pinned checkout — every claim confirmed (`Measurable.find`:507, `cauchySeq_of_le_geometric`:528, `measurable_of_tendsto_metrizable`:51, `IsClosed.mem_iff_infDist_zero`:697, `infDist_le_dist_of_mem`:617, `continuous_infDist_pt`:673, `upgradeIsCompletelyMetrizable`:205, `denseSeq`/`exists_dense_seq`/`denseRange_denseSeq`:337/328/342, `isTightMeasureSet_singleton` Tight.lean:103, `ProbabilityMeasure.continuous_map` ProbabilityMeasure.lean:653, project `isTightMeasureSet_of_cauchySeq` ProbabilityMeasurePolish.lean:156). KRN still MISSING from Mathlib (no measure-theoretic `selection`/`selector` hits; no set-valued measurability API).

---

## 0. Executive summary

- **Mathlib status: KRN is MISSING.** No measurable-selection theorem for set-valued
  maps exists anywhere in this Mathlib (details §1). All *ingredients* for the
  classical proof are present and confirmed by name (§2.3).
- **KRN itself: GO** — self-contained, ~350 lines, low risk, also a genuine Mathlib
  upstream candidate (not even listed in `docs/1000.yaml`).
- **KRN as a replacement for JvN in Phase 4 (ε-optimal selection): NO-GO.**
  The ε-optimal subset of `Feas t h` is **not closed-valued** in the current Borel
  model (VGo is lower semi*analytic*, not lsc, so `γ ↦ ∫⁻ VGo dγ` is not lsc and its
  sublevel sets are not closed). This is the Bertsekas–Shreve dichotomy; Blackwell-type
  counterexamples show Borel ε-optimal selectors do not exist in general in the Borel
  model. σ(Σ¹₁) via `jankov_von_neumann` is essentially sharp there. Honest verdict in §4.
- **What KRN DOES buy us (real, new):** a **plain-Borel-measurable FEASIBLE selector**
  `h ↦ γ(h) ∈ Feas t h` — i.e. measurable bicausal Markov strategies exist — because
  `Feas t h` is closed AND **compact** (couplings of fixed marginals are tight +
  Prokhorov), and compactness rescues the weak-measurability hypothesis at the Borel
  level (§4.2; the graph-projection route alone would only give Σ¹₁ hit-sets and land
  back in σ(Σ¹₁)). Package cost: KRN ~350 + Feas weak-measurability ~250 ≈ **600 lines**.
- **Long-range upgrade path** (separate future phase, do not start now): under a
  *semicontinuous model* (Feller kernels + lsc costs), KRN + Berge machinery gives
  **exact Borel-measurable optimal strategies** — strictly stronger conclusions under
  strictly stronger hypotheses; ~800–1200 additional lines (§4.3).

Recommendation: treat E3 as a **parallel side-front** (new files only, zero contact
with Phase 3/4 main line). Attack order: KRN core → Feas hit-set measurability →
`exists_measurable_feasible_strategy`. Do not let it preempt Phase 3.

---

## 1. Mathlib recon: what exists / what is missing

### 1.1 MISSING (searched thoroughly, no hits)

| Search | Result |
|---|---|
| `Kuratowski`, `RyllNardzewski`, `Ryll-Nardzewski` | Only `Topology/MetricSpace/Kuratowski.lean` (Kuratowski *embedding* into ℓ∞), ZFC Kuratowski pairs, Archive items, and the Ryll-Nardzewski *fixed-point* theorem entry in `docs/1000.yaml`. Nothing about selection. |
| `selection`, `selector` (case-insensitive, all of Mathlib) | Only tactic/widget internals, `Order/Iterate`, linear algebra — zero measure-theoretic hits. |
| `Castaing`, `Effros`, `Himmelberg`, `Aumann`, `Filippov` | Zero relevant hits (only category-theory files matching by accident). |
| `uniformization`, `von Neumann` (measure-theoretic) | Nothing selection-related. |
| multifunction / set-valued measurability | No API at all. Mathlib has **no notion of measurable set-valued map**. |
| `docs/1000.yaml` | Lists Blaschke/Helly selection theorems (unrelated); the KRN measurable selection theorem is **not even listed**. |

Closest existing relatives (none subsume KRN):
- `MeasurableEmbedding` inverse machinery, `exists_measurableEmbedding_real`
  (`MeasureTheory/Constructions/Polish/EmbeddingReal.lean`) — selection only for
  graphs of injective measurable maps.
- Our own project: `jankov_von_neumann` (Tree.lean:284) — σ(Σ¹₁)-measurable
  uniformization of **analytic** sets, and `jvn_closedG` (Tree.lean:270) for closed
  `F ⊆ X × ℕ^ℕ`. Note `jvn_closedG` is *morally* a KRN special case but the selector
  is only `AnalyticallyMeasurable`, and the hypothesis is a closed **graph**, not a
  weakly measurable multifunction.

**Verdict: MISSING, as expected. Formalization is from scratch (but small).**

### 1.2 Ingredients CONFIRMED present (exact names, this Mathlib checkout)

- `TopologicalSpace.exists_dense_seq` / `denseSeq` / `denseRange_denseSeq`
  (`Topology/Bases.lean:328–343`) — countable dense sequence, needs `[SeparableSpace] [Nonempty]`.
- `Measurable.find` (`MeasureTheory/MeasurableSpace/Constructions.lean:507`):
  `(hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet {x | p n x}) (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x`
  — exactly the "least dense point satisfying a measurable predicate" combinator;
  also raw `measurable_find`. (Needs `DecidablePred`; `Classical.dec` fine.)
- `cauchySeq_of_le_geometric` (`Analysis/SpecificLimits/Basic.lean:528`):
  `dist (f n) (f (n+1)) ≤ C * r^n`, `r < 1` ⇒ `CauchySeq f`; also
  `cauchySeq_of_le_tendsto_0` (`Topology/MetricSpace/Cauchy.lean:103`) as fallback.
- `cauchySeq_tendsto_of_complete` (`Topology/UniformSpace/Cauchy.lean:429`).
- `measurable_of_tendsto_metrizable` (`MeasureTheory/Constructions/BorelSpace/Metrizable.lean:51`)
  — **domain is an arbitrary `[MeasurableSpace α]`**, exactly what KRN needs (abstract
  σ-algebra 𝒜, not Borel); codomain `[PseudoMetrizableSpace β] [BorelSpace β]`.
- `Metric.infDist` API (`Topology/MetricSpace/HausdorffDistance.lean`):
  `infDist_le_dist_of_mem` (:617), `continuous_infDist_pt` (:673),
  `IsClosed.mem_iff_infDist_zero` (:697), `infDist_nonneg`.
- `upgradeIsCompletelyMetrizable` (`Topology/Metrizable/CompletelyMetrizable.lean:205`)
  — the `[PolishSpace Y]` → metric+complete+separable upgrade for the wrapper.
- `IsClosed.isGδ` (`Topology/Separation/GDelta.lean:113`, `[PerfectlyNormalSpace]`) —
  gives open = Fσ in metrizable spaces (needed only in the *application*, §4.2).
- `tendsto_pow_atTop_nhds_zero_of_lt_one` for the squeeze at the end.

Nothing else is required. **All prerequisites exist under confirmed names.**

---

## 2. KRN formalization plan

New file suggestion: `BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean`
(namespace `MeasurableSelection` or top-level per project style).

### 2.1 Statement (Lean-like, target form)

```lean
open Metric TopologicalSpace

variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- The set of points whose fiber hits `U`. -/
def hitSet (Φ : α → Set Y) (U : Set Y) : Set α := {a | (Φ a ∩ U).Nonempty}

/-- **Kuratowski–Ryll-Nardzewski measurable selection theorem** (Kechris 12.13,
Srivastava 5.2.1). A closed-nonempty-valued, weakly measurable multifunction into a
Polish space admits a measurable selector. -/
theorem exists_measurable_selection {Φ : α → Set Y}
    (hclosed : ∀ a, IsClosed (Φ a)) (hne : ∀ a, (Φ a).Nonempty)
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet (hitSet Φ U)) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a
```

Design notes:
- Standing instances mirror §3W's "upgraded Polish" pattern; add a thin wrapper
  `exists_measurable_selection_polish` for `[TopologicalSpace Y] [PolishSpace Y]
  [BorelSpace Y]` via `letI := upgradeIsCompletelyMetrizable Y` (PolishSpace extends
  IsCompletelyMetrizableSpace + second countable ⇒ separable). CAUTION: the upgraded
  metric must induce the *same* topology (it does — that is the point of the upgrade)
  so `BorelSpace Y` is unambiguous.
- `Nonempty Y` follows from `hne a` at any `a` only if `α` is nonempty; take
  `[Nonempty Y]` OR case-split `isEmpty_or_nonempty α` (empty α: `f := (hne · |>.choose)`
  vacuously measurable — actually `Measurable` from `Subsingleton (Set α)`… simplest:
  require `[Nonempty Y]` in the core lemma, discharge in the wrapper by cases on
  `isEmpty_or_nonempty α`, using `denseSeq` needs `Nonempty Y` anyway).
- The hypothesis `hmeas` is only *used* on countably many open balls
  `ball (denseSeq Y n) r`; do NOT weaken the statement (standard form is ∀ open U,
  and the ball form is equivalent via Lindelöf) — but this means the proof never
  needs measurability of arbitrary hit-sets, which keeps the application cheap.

### 2.2 Proof at lemma granularity

Classical scheme: iterate over the dense sequence `y := denseSeq Y`, building
countably-valued measurable `2⁻ᵏ`-approximate selectors that form a uniform Cauchy
sequence; the limit is the selector.

**K1 (index recursion — the workhorse).** Define, for `k : ℕ`, the "approximation
level k" predicate and the step. Cleanest Lean shape: a Σ-type carrying the invariant
(pattern proven in Capacitability.lean's `capAux`):

```lean
/-- Approximate selectors: measurable, countably-valued via an index function,
    with fibers hit within radius (1/2)^k. -/
def ApproxSel (Φ : α → Set Y) (k : ℕ) :=
  { g : α → Y // Measurable g ∧ ∀ a, (Φ a ∩ ball (g a) ((1/2)^k)).Nonempty }
```

- **K1a (base).** `g₀ a := y (Nat.find (h₀ a))` where
  `h₀ a : ∃ n, (Φ a ∩ ball (y n) 1).Nonempty` — existence: pick `x ∈ Φ a` (hne),
  `denseRange_denseSeq` gives `y n ∈ ball x 1`, symmetry of dist. Wait: need
  `x ∈ ball (y n) 1` — same thing by `dist_comm`. Measurability: `Measurable.find`
  with `f n := fun _ => y n` (constant), `hp n := hmeas _ isOpen_ball`.
  Radius bookkeeping: `(1/2)^0 = 1`. ~30 lines.
- **K1b (step).** Given `⟨g, hg_meas, hg_hit⟩ : ApproxSel Φ k`, define
  `p m a := (Φ a ∩ ball (y m) ((1/2)^(k+1))).Nonempty ∧ dist (y m) (g a) < (1/2)^k + (1/2)^(k+1)`.
  - Existence `∀ a, ∃ m, p m a`: by `hg_hit a` pick `x ∈ Φ a ∩ ball (g a) ((1/2)^k)`;
    density gives `m` with `dist (y m) x < (1/2)^(k+1)`; triangle inequality gives
    both conjuncts.
  - Measurability of `{a | p m a}`: first conjunct is `hmeas _ isOpen_ball`; second
    is `g ⁻¹' (ball (y m) c)` — `hg_meas (isOpen_ball.measurableSet)` (NOTE: written
    as a preimage of an open ball *centered at y m* using `dist_comm`; no partition
    over the countable range of g needed — this is the main simplification over the
    textbook proof).
  - Output `g' a := y (Nat.find (hex a))`, again `Measurable.find`.
  - Extra spec to carry OUT of the subtype (returned alongside, or as a separate
    lemma consuming the definitional unfolding): `∀ a, dist (g' a) (g a) < 3 * (1/2)^(k+1)`
    (from the second conjunct: `(1/2)^k + (1/2)^(k+1) = 3·(1/2)^(k+1)`). ~80 lines.
- **K1c (assembly).** `approx : (k : ℕ) → ApproxSel Φ k := Nat.rec K1a (fun k ih => (K1b ih).1)`
  — plus the consecutive-distance lemma
  `dist_approx_succ : ∀ k a, dist ((approx (k+1)).1 a) ((approx k).1 a) ≤ 3 * (1/2)^(k+1)`
  by `rfl`-unfolding of the recursion + K1b's spec. If the equation compiler fights
  the Σ-type recursion, fall back to a single `theorem exists_approx : ∀ k, ∃ g : ApproxSel Φ k, ...`
  chain with `choose` — but the explicit `Nat.rec` is preferred (no choice juggling,
  matches capAux style). ~50 lines.

**K2 (Cauchy + limit).** For fixed `a`: `dist (F k a) (F (k+1) a) ≤ (3/2) * (1/2)^k`
(rewrite `3·(1/2)^(k+1)`), so `cauchySeq_of_le_geometric (C := 3/2) (r := 1/2)`;
`cauchySeq_tendsto_of_complete` yields the pointwise limit. Define
`f a := (K2cauchy a).choose`, `hf_tendsto a := (K2cauchy a).choose_spec`.
Convert pointwise tendsto to `Tendsto (fun k => F k) atTop (𝓝 f)` via
`tendsto_pi_nhds`; conclude `Measurable f` by `measurable_of_tendsto_metrizable`.
~50 lines.

**K3 (membership).** `infDist (F k a) (Φ a) < (1/2)^k` by `hg_hit` +
`infDist_le_dist_of_mem` (+ `dist_comm`). Then
`Tendsto (fun k => infDist (F k a) (Φ a)) atTop (𝓝 (infDist (f a) (Φ a)))`
by `(continuous_infDist_pt (Φ a)).tendsto.comp (hf_tendsto a)`; squeeze against
`tendsto_pow_atTop_nhds_zero_of_lt_one` (via `le_of_tendsto_of_tendsto'` /
`ge_of_tendsto'` + `infDist_nonneg`) gives `infDist (f a) (Φ a) = 0`; finish with
`(hclosed a).mem_iff_infDist_zero (hne a)`. ~40 lines.

**K4 (main theorem + wrapper + docstrings).** Assemble; PolishSpace wrapper;
wire into `Basic.lean` + `AxiomsAudit.lean`. ~40 lines.

### 2.3 Size & risk estimate

| Node | Lines | Risk |
|---|---|---|
| defs + preamble | 25 | — |
| K1a base | 30 | low |
| K1b step | 80 | low-medium (Nat.find spec extraction; `1/2` real-arithmetic normalization — use `(2⁻¹ : ℝ)^k` or `(1/2 : ℝ)^k` consistently, `norm_num`-friendly) |
| K1c recursion | 50 | medium (Σ-type `Nat.rec` defeq; fallback path known) |
| K2 Cauchy/limit | 50 | low |
| K3 membership | 40 | low |
| K4 assembly | 40 | low |
| **Total** | **~315 (est. 300–400)** | **LOW overall** |

Comparable to Tree.lean (315 lines, 5 compile rounds). No new mathematics; every
external lemma verified present by exact name. Expected compile-fix rounds: 3–6.
Known friction to expect (project battle-log patterns): `(1/2 : ℝ)` vs `2⁻¹` powers
(`one_div`, `pow_succ` normalization); `Nat.find` needs `DecidablePred` — open a
`Classical` section; `Measurable.find`'s `f : ℕ → α → β` shape wants constants
`fun n _ => y n`.

---

## 3. Sanity check performed for the application: is `Feas t h` closed in the weak topology?

**YES** (as conjectured in the front prompt). After the Phase-3 reindexing over
`P(W) = ProbabilityMeasure W` (battle log 2026-07-04): with `μh := κμ t (projX t h)`,
`Feas t h = (P.map fst)⁻¹ {μh} ∩ (P.map snd)⁻¹ {νh}` where
`ProbabilityMeasure.map` along the continuous `Prod.fst` is continuous
(`ProbabilityMeasure.continuous_map`, confirmed in §7 recon notes), and singletons
are closed since `P(X)` is T2 — metrizable via the LP homeomorphism (our W1,
`ProbabilityMeasurePolish.lean`). Preimage of closed under continuous ∩ likewise = closed. ∎

**Moreover — and this is the load-bearing bonus — `Feas t h` is COMPACT:**
it is closed (above) and tight: for `γ ∈ Feas t h`,
`γ ((K₁ ×ˢ K₂)ᶜ) ≤ μh K₁ᶜ + νh K₂ᶜ` (complement of a product ⊆ union of two slabs;
marginal identities), and `{μh}`, `{νh}` are tight (`isTightMeasureSet_singleton`,
Mathlib, Polish). Closed + tight ⇒ compact by Prokhorov
(`isCompact_closure_of_isTightMeasureSet`, Mathlib, already battle-tested in our C1).
Compactness is what rescues Borel weak-measurability below.

---

## 4. CRITICAL ASSESSMENT: what KRN buys over the JvN route — honest version

Baseline (what we already have): `jankov_von_neumann` gives σ(Σ¹₁)-measurable
uniformization of ANALYTIC sets; Phase 4 plans to apply it to the ε-optimal set
`Aε = {(h,γ) ∈ Γ : F(h,γ) < inf-fiber + ε}` (analytic), yielding σ(Σ¹₁)-measurable
ε-optimal strategies (BS 7.50 analogue).

### 4.1 The front prompt's hoped-for upgrade — and its flaw

Hope: "Feas has closed fibers, so KRN gives plain-Borel ε-optimal strategies,
strictly better than σ(Σ¹₁)."

**The flaw: the multifunction that must be selected from for Phase 4 is not `Feas`
but the ε-optimal subset** `Aε(h) = {γ ∈ Feas t h : F(h,γ) ≤ g(h) + ε}` where
`F(h,γ) = ∫⁻ z, VGo k (t+1) (h,z) ∂γ` and `g = inf-fiber`. KRN needs `Aε(h)` CLOSED.
Sublevel sets `{γ : F(h,·) ≤ c}` are closed iff `F(h,·)` is lsc on `P(W)`, which by
portmanteau requires the integrand `z ↦ VGo k (t+1) (h,z)` to be lsc. Phase 3 gives
only **lower semianalytic** — and that is not a proof deficiency but intrinsic to the
Borel model (Borel kernels, lsa costs): VGo genuinely fails to be lsc, and even fails
to be Borel in general. So `Aε` is closed-valued in NO useful generality, and KRN
does not apply to it. Trying to rescue via `closure (Aε h)` fails: points of the
closure need not be ε-optimal (F not usc).

Deeper obstruction (why no clever fix exists): this is exactly the
Bertsekas–Shreve dichotomy (BS Ch. 7–8). In the Borel model, Blackwell-type
counterexamples show **Borel-measurable ε-optimal selectors do not exist in
general**; universally-/analytically-measurable is sharp. Hence:

> **NO-GO on "KRN replaces JvN in Phase 4."** Not merely harder — mathematically
> impossible under current hypotheses. `jankov_von_neumann` stays.

### 4.2 What IS genuinely reachable: Borel-measurable FEASIBLE strategies (new deliverable)

Apply KRN to `Φ h := Feas t h` itself (closed ✓, nonempty ✓ by hypothesis `hne`).
Remaining KRN hypothesis: weak measurability
`∀ U open, {h | Feas t h ∩ U ≠ ∅} ∈ Borel(PairHist t)`.

- **Warning (the catch, as flagged in the front prompt):** the lazy route —
  hit-set = `proj_h (Γ ∩ (univ ×ˢ U))` with Γ Borel — only gives ANALYTIC hit-sets;
  KRN then runs over 𝒜 = σ(Σ¹₁) and returns a σ(Σ¹₁) selector: **zero improvement**
  over JvN. The Borel claim needs a real argument.
- **The real argument (compactness route), all tools in hand:** factor through
  `m : h ↦ (μh, νh) : PairHist t → P(X) × P(Y)` (Borel: kernel measurability + W2
  reasoning already used for Γ in Phase 3 plan) and the fixed correspondence
  `Π : (μ,ν) ↦ CouplingSet(μ,ν) ⊆ P(W)`. Then:
  - **E3-A (tight couplings).** `S ⊆ P(X)`, `T ⊆ P(Y)` tight ⇒
    `⋃ {Π(μ,ν) : μ ∈ S, ν ∈ T}` tight. Proof: product-compact + slab bound of §3.
    (~60 lines; uses `IsTightMeasureSet` API + `IsCompact.prod`.)
  - **E3-B (closed hit-sets against closed targets).** For `C ⊆ P(W)` closed:
    `H_C := {(μ,ν) | (Π(μ,ν) ∩ C).Nonempty}` is CLOSED. Proof: sequential (all
    spaces metrizable by W1): `(μₙ,νₙ) → (μ,ν)`, `γₙ ∈ Π(μₙ,νₙ) ∩ C`; the convergent
    marginal sequences are LP-Cauchy, hence tight by OUR `isTightMeasureSet_of_cauchySeq`
    (ProbabilityMeasurePolish.lean:156); E3-A ⇒ `{γₙ}` tight; Prokhorov
    (`isCompact_closure_of_isTightMeasureSet`) + metrizability ⇒ convergent
    subsequence `γ* `; marginal maps continuous ⇒ `γ* ∈ Π(μ,ν)`; C closed ⇒ `γ* ∈ C`.
    (~100 lines — the single biggest new lemma.)
  - **E3-C (open = Fσ + assembly).** U open in metrizable `P(W)` is a countable
    union of closed sets (`(IsClosed.isGδ Uᶜ)` complemented, or inline
    `Cₙ := {γ | 1/(n+1) ≤ infDist γ Uᶜ}`); `hitSet Φ U = m⁻¹ (⋃ₙ H_{Cₙ})` — wait,
    hit-sets against a union: `Π ∩ U ≠ ∅ ↔ ∃ n, Π ∩ Cₙ ≠ ∅` (⊆ direction: any
    `γ ∈ Π ∩ U` lies in some `Cₙ`) ✓. Borel. (~40 lines.)
  - **E3-D (deliverable).** KRN ⇒
    `exists_measurable_feasible_strategy : ∃ γ : PairHist t → P(W), Measurable γ ∧ ∀ h, γ h ∈ Feas t h`
    — plain Borel measurability. Currently the project has only pointwise-choice
    feasible strategies (L3 machinery); this is a clean, citable upgrade
    ("measurable bicausal Markov strategies exist") and independently meaningful
    for stating kernel-valued strategies. (~50 lines wiring.)

  Package cost beyond KRN: **~250 lines**, all on top of already-green W1 machinery.
  Dependencies: Phase-3 prerequisite instances for PairHist topology + the kernel
  measurability of `m` (shared with Phase 3 — so E3-D lands naturally AFTER the
  Phase-3 prerequisite drops, or can take `Measurable m` as a hypothesis to decouple).

### 4.3 Long-range payoff: the semicontinuous model (future phase, not now)

If we later add hypotheses "κμ, κν Feller (weakly continuous in h)" and "c t lsc"
(BS Ch. 8.3 lower-semicontinuous model), then by backward induction VGo becomes
genuinely **lsc** (needs: portmanteau lsc of `γ ↦ ∫⁻ f dγ` for lsc f; Berge-type
"inf over a continuous compact-valued correspondence of an lsc function is lsc";
**lower hemicontinuity of `(μ,ν) ↦ Π(μ,ν)`** — a real gluing-construction lemma,
~150–250 lines, the hard new ingredient). Then the EXACT argmin correspondence
`h ↦ {γ ∈ Feas h : F(h,γ) = min}` is nonempty (lsc attains min on compact Feas),
compact/closed-valued, weakly measurable (measurable-maximum-theorem argument built
on E3-B-style hit-sets), and KRN yields **exact Borel-measurable optimal
strategies** — strictly stronger conclusion than Phase 4's, under strictly stronger
hypotheses (incomparable with, not dominating, the JvN result; both are worth
having, mirroring BS's twin-track presentation). Estimated additional cost beyond
the §4.2 package: ~800–1200 lines. Park as "Phase 5 candidate"; decide after
Phase 4.

### 4.4 Verdict table

| Move | Verdict | Cost | Value |
|---|---|---|---|
| KRN core theorem | **GO** | ~350 lines, low risk | Arsenal piece; Mathlib-missing (upstream candidate); prerequisite for everything below |
| Borel feasible selector for Feas (E3-A…D) | **GO (after/with Phase-3 prereqs)** | +~250 lines | New theorem: measurable bicausal strategies; exercises W1 exactly where it's strongest (tightness/Prokhorov) |
| Replace JvN σ(Σ¹₁) in Phase 4 ε-optimal selection | **NO-GO** | — | Impossible in the Borel model (Aε not closed-valued; Blackwell counterexamples); JvN remains the right tool |
| Semicontinuous model, exact Borel optima | **DEFER (Phase 5 candidate)** | +~800–1200 lines | Strictly stronger conclusions under Feller+lsc hypotheses |

### 4.5 Priority recommendation

E3 is strictly parallel to the Phase 3 main line (new files; only soft dependency is
`Measurable m`, which can be hypothesized away). Recommended: formalize KRN core now
via a side agent (it is self-contained and low-risk), hold E3-A…D until Phase 3's
PairHist-topology + kernel-measurability prerequisites land, and keep Phase 4 on the
JvN route unchanged.
