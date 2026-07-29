# BLUEPRINT — Multi-period Bellman recursion for bicausal OT

> **Purpose.** This is the external memory and battle plan for the campaign
> extending the verified T=1 Bellman recursion to general finite horizon T,
> then to semianalyticity of value functions and measurable selection.
> It is written to be self-contained: a fresh session should be able to
> resume the war from this file alone plus the repository.
>
> **How to resume:** read this file top to bottom, check the Battle Log
> (§7) for the current front line, run `lake build` to confirm the base is
> green, then attack the first non-green node of the active phase.
>
> **Standing orders (from the user, 2026-07-03):** self-directed — write
> the plan, review it yourself, formalize it. Requirements: 0 sorry,
> 0 custom axiom, 0 error, 0 warning. Match existing project style
> (top-level theorems, doc comments, `variable` sections).

Status legend: `[DONE]` verified in Lean · `[READY]` all dependencies done,
attack now · `[PLANNED]` informal proof written below · `[WALL?]` risk,
needs reconnaissance · `[SCOUTED]` recon done, see notes.

---

## §1. Current arsenal (all [DONE], `lake build` green as of 2026-07-03)

Toolchain v4.29.0-rc8,
Mathlib pinned in lake-manifest. 20 theorems pass `#print axioms` with only
`[propext, Classical.choice, Quot.sound]` (see `BicausalOT/AxiomsAudit.lean`).

- T=1 value representation: `bellman_value_eq` (ValueRepresentation.lean),
  with `V₀_le_cost_pointwise`, `bellman_lower_bound`, `eps_optimal_element`,
  `eps_optimal_selection` (pointwise choice, no measurability),
  `eps_optimal_kernel_bound`, `totalCost_le_V₀_plus_eps`.
- Definitions (Defs.lean): `CouplingSet₀ μ₀ ν₀`, `FeasibleSet₀ κ_μ κ_ν z₀`,
  `KernelDecomp`, `IsBicausal₂`, `V₀`, `totalCost`.
- DST library: `jankov_von_neumann` (Tree.lean, σ(Σ¹₁)-measurable
  uniformization of analytic sets), `analyticMeasurableSpace`,
  `AnalyticallyMeasurable`, `IsLowerSemianalytic`,
  `IsLowerSemianalytic.iInf_fiber` (BS 7.47).
- NEW (this campaign's precursors, 2026-07-03):
  - `MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact` — Choquet
    capacitability, Capacitability.lean. Souslin scheme
    `capScheme π s n = closure (π '' cylinder s n)`; compact witness
    `π '' capBelow β`; core lemma `iInter_capW_subset`; recursion
    `capAux`/`capBound`/`cap_exists_bound` over an abstract monotone
    functional `m` with countable-increasing-sup continuity.
  - `MeasureTheory.AnalyticSet.nullMeasurableSet` — universal measurability.
  - `MeasureTheory.AnalyticSet.kernel_section_gt` — parametrized
    capacitability: A analytic in X×Y, κ finite kernel ⇒
    `{x | c < κ x (Prod.mk x ⁻¹' A)}` analytic.
  - `lintegral_lowerSemianalytic` (KernelIntegral.lean) — BS 7.48 for
    Markov kernels. Helpers there worth reusing:
    `MeasureTheory.AnalyticSet.preimage_of_continuous` (graph trick),
    `MeasureTheory.AnalyticSet.inter'`, `.union'`, `.prod_apply`
    (null-measurable Fubini), `aemeasurable_of_analytic_sublevels`,
    `ennreal_le_iff_forall_lt_add_inv`, `ennreal_iSup_min_natCast`,
    `volume_restrict_epigraph_section`.

Key design fact inherited from T=1: **infima range over arbitrary function
families, not measurable kernels.** `∫⁻` is defined for arbitrary
integrands; ε-optimal selection is pointwise `choose`. This makes Phases
1–2 measurability-free.

---

## §2. Phase 1–2: T-period value representation  [PLANNED — attack first]

### 2.1 Design decisions (settled, do not relitigate)

- **Nested-product histories, not `Fin`-indexed functions.**
  `PairHist (t+1) := PairHist t × (X (t+1) × Y (t+1))`. Appending a step is
  literally pairing `(h, z)`; no dependent reindexing, no `Fin.snoc`.
- **Time-to-go recursion.** All recursive definitions take the number of
  remaining periods `k` as the structural argument:
  `costGo`/`VGo : (k t : ℕ) → PairHist t → …`. Structural recursion on `k`,
  no `termination_by` friction. Horizon `T` appears only in the final
  theorem (`k := T`, `t := 0`).
- **No `MeasurableSpace` on `PairHist` needed in Phases 1–2.** Integrals
  are only over one-step measures on `X (t+1) × Y (t+1)` (instances exist);
  history is a bound variable of the integrand. `projX/projY` are plain
  functions used only to STATE feasibility.
- **Stage costs `c : (t : ℕ) → PairHist t → ℝ≥0∞`** paid on the history at
  each time, including the terminal one (`costGo 0 t h = c t h`). The T=1
  theorem is the instance T=1 with `c 0 = c₀`, `c 1 (h₀,z₁) = c₁ (h₀,z₁)`.
- Stage-0 coupling is a plain measure `γinit ∈ CouplingSet₀ μ₀ ν₀` (reuse
  the existing definition); stages ≥ 1 are function-families ("strategies").

### 2.2 Definitions (file `BicausalOT/MultiPeriod.lean`, namespace `MultiPeriod`)

- D1 `PairHist X Y : ℕ → Type*` — `0 ↦ X 0 × Y 0`, `t+1 ↦ PairHist t × (X (t+1) × Y (t+1))`.
- D2 `XHist X : ℕ → Type*`, `YHist Y : ℕ → Type*` — same shape, single side.
- D3 `projX : ∀ t, PairHist X Y t → XHist X t` — `0: h ↦ h.1`,
  `t+1: (h,z) ↦ (projX t h, z.1)`; `projY` symmetric.
- D4 data: `κμ : (t : ℕ) → XHist X t → Measure (X (t+1))`,
  `κν : (t : ℕ) → YHist Y t → Measure (Y (t+1))`,
  `c : (t : ℕ) → PairHist X Y t → ℝ≥0∞`.
- D5 `Feas κμ κν t h : Set (Measure (X (t+1) × Y (t+1))) :=
  {γ | γ.map Prod.fst = κμ t (projX t h) ∧ γ.map Prod.snd = κν t (projY t h)}`.
- D6 `Strat X Y := (t : ℕ) → (h : PairHist X Y t) → Measure (X (t+1) × Y (t+1))`.
- D7 `costGo c γ : (k t : ℕ) → PairHist t → ℝ≥0∞`:
  `costGo 0 t h = c t h`;
  `costGo (k+1) t h = c t h + ∫⁻ z, costGo k (t+1) (h, z) ∂(γ t h)`.
- D8 `VGo κμ κν c : (k t : ℕ) → PairHist t → ℝ≥0∞`:
  `VGo 0 t h = c t h`;
  `VGo (k+1) t h = c t h + ⨅ (γm) (_ : γm ∈ Feas κμ κν t h), ∫⁻ z, VGo k (t+1) (h, z) ∂γm`.

### 2.3 Lemmas with proofs (formalization granularity)

- **L0 (mass of feasible measures).** If `IsProbabilityMeasure (κμ t x)`
  for all t x, and `γm ∈ Feas t h`, then `γm univ = 1`.
  *Proof.* `γm univ = (γm.map Prod.fst) univ` (map preserves total mass:
  `Measure.map_apply` on univ, or `measure_univ` via
  `Measure.map_apply measurable_fst .univ`; preimage of univ is univ)
  `= κμ t (projX t h) univ = 1`. Beware: `map_apply` needs measurability
  of `Prod.fst` — available. Alternative: rewrite with the feasibility
  equation and use `Measure.measure_univ_map`-style lemma; if absent,
  `(congrArg (fun m => m univ) hfeas.1)` then `Measure.map_apply
  measurable_fst MeasurableSet.univ` with `preimage_univ`.
- **L1 (pointwise bound).** `γm ∈ Feas t h →
  VGo (k+1) t h ≤ c t h + ∫⁻ z, VGo k (t+1) (h,z) ∂γm.`
  *Proof.* unfold `VGo`; `add_le_add_left (iInf₂_le γm hmem)` — mirror of
  `V₀_le_cost_pointwise` (LowerBound.lean uses `gcongr; exact iInf₂_le γ hγ`).
- **L2 (value ≤ cost, pointwise in history).** For `γ : Strat` with
  `∀ t h, γ t h ∈ Feas t h`: `∀ k t h, VGo k t h ≤ costGo k t h γ`.
  *Proof.* Induction on k. k=0: both sides `c t h`. k+1: L1 with
  `γm := γ t h`, then `lintegral_mono` with the induction hypothesis at
  `(t+1, (h,z))`. Lean: recursive `theorem … | 0 … | k+1 …` or induction
  tactic; the IH is used inside `lintegral_mono fun z => …` — fine since
  the recursion is on k only.
- **L3 (ε-optimal strategy).** If every `Feas t h` is nonempty and ε > 0,
  there is `γε : Strat` with (i) `∀ t h, γε t h ∈ Feas t h` and (ii)
  `∀ k t h, ∫⁻ z, VGo k (t+1) (h,z) ∂(γε t h) ≤
   (⨅ (γm) (_ : γm ∈ Feas t h), ∫⁻ z, VGo k (t+1) (h,z) ∂γm) + ε`?
  **CAUTION:** (ii) as stated quantifies over all k for a single γε — the
  infimum depends on k, one measure cannot be ε-optimal for every k
  simultaneously. FIX: the strategy only ever gets evaluated at the
  time-consistent depth. Two clean options:
  (a) build γε for a FIXED horizon T: at stage t use integrand
      `VGo (T - t - 1) (t+1)`; state (ii) only for `k = T - t - 1` — wait,
      `t` ranges over ℕ beyond T; for `t ≥ T` pick any feasible element
      (nonemptiness). Since costGo T 0 only evaluates γ at stages
      t < T with depth exactly T−t−1, this suffices.
  (b) make Strat depth-indexed. REJECTED — pollutes all definitions.
  Adopt (a): `theorem exists_eps_strategy (T : ℕ) (hne) (hε : 0 < ε) :
  ∃ γε, (∀ t h, γε t h ∈ Feas t h) ∧ ∀ t (h : PairHist t), t < T →
  ∫⁻ z, VGo (T-t-1) (t+1) (h,z) ∂(γε t h) ≤ (⨅ …) + ε`.
  *Proof.* pointwise: for each (t,h) with t < T apply `eps_optimal_element`
  (UpperBound.lean — it is stated for arbitrary α, S : Set α, f : α → ℝ≥0∞:
  exactly reusable) to `S := Feas t h`,
  `f := fun γm => ∫⁻ z, VGo (T-t-1) (t+1) (h,z) ∂γm`; for t ≥ T pick
  `(hne t h).choose`. Assemble with `choose` / explicit dite. Lean detail:
  define `γε t h := if ht : t < T then (key t h ht).choose else (hne t h).choose`
  where `key` is the ∃-statement; extract the two properties.
- **L4 (ε upper bound).** κ's Markov, γε from L3 (horizon T). Then for all
  t ≤ T … formulate on time-to-go: `∀ k t h, t + k = T →
  costGo k t h γε ≤ VGo k t h + k • ε` (use `k * ε` in ℝ≥0∞, i.e.
  `(k : ℝ≥0∞) * ε`). *Proof.* Induction on k with t moving: k=0 trivial.
  k+1 (so t + k + 1 = T, hence t < T and (T−t−1) = k):
  `costGo (k+1) t h γε = c t h + ∫⁻ z, costGo k (t+1) (h,z) γε ∂(γε t h)`
  `≤ c t h + ∫⁻ z, (VGo k (t+1) (h,z) + k*ε) ∂(γε t h)` (lintegral_mono, IH
  with t+1 + k = T) `= c t h + ∫⁻ z, VGo k (t+1) (h,z) ∂(γε t h) + k*ε`
  (`lintegral_add_right _ measurable_const`, `lintegral_const`, mass 1 by
  L0) `≤ c t h + ((⨅ …) + ε) + k*ε` (L3(ii), depth matches: T−t−1 = k)
  `= VGo (k+1) t h + (k+1)*ε` (unfold VGo, ring_nf on ℝ≥0∞ additions —
  push_cast for `((k+1 : ℕ) : ℝ≥0∞)`; all finite additions, no tsub).
- **L5 (integrated bounds and main theorem).** Hypotheses: `[IsProbabilityMeasure μ₀]
  [IsProbabilityMeasure ν₀]`, `hκμ : ∀ t x, IsProbabilityMeasure (κμ t x)`,
  `hκν` symmetric (only one side needed for L0 — keep both for symmetry),
  `hne : ∀ t h, (Feas t h).Nonempty`,
  `hprob₀ : ∀ γ₀ ∈ CouplingSet₀ μ₀ ν₀, γ₀ univ ≤ 1` (as in T=1; provable
  from probability marginals but T=1 took it as hypothesis — DO THE SAME
  for fidelity, or prove it via L0-style argument and drop the hypothesis;
  decide at the front: proving it is 3 lines with map_apply, prefer proving).
  **Theorem `bellman_value_eq_multi` (T : ℕ):**
  `⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
     (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀) (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
     ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
   = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
     ∫⁻ h₀, VGo κμ κν c T 0 h₀ ∂γ₀`.
  *Proof.* `le_antisymm`.
  (≥ direction, mirror `bellman_value_geq`): fix γ₀, γ, memberships; RHS-inf
  ≤ ∫ VGo T 0 dγ₀ ≤ ∫ costGo dγ₀ (L2 pointwise + lintegral_mono); chain
  `iInf₂_le` / `le_iInf`.
  (≤ direction, mirror `bellman_value_leq`): fix γ₀ ∈ Π; apply
  `ENNReal.le_of_forall_pos_le_add`; given ε > 0 (ℝ≥0) with RHS < ∞:
  if T = 0: costGo 0 = VGo 0 = c 0, trivial equality — handle first
  (`rcases Nat.eq_zero_or_pos T`); if T ≥ 1: set δ := ε / T (in ℝ≥0∞:
  `(ε : ℝ≥0∞) / T`, positive since ε > 0, T ≠ 0, T ≠ ∞); L3 with δ; L4 at
  (k,t) = (T,0) gives `costGo T 0 h₀ γδ ≤ VGo T 0 h₀ + T*δ` pointwise;
  integrate (`lintegral_mono`, `lintegral_add_right`, `lintegral_const`,
  γ₀ univ = 1); `T * (ε/T) = ε`: `ENNReal.mul_div_cancel'` needs T ≠ 0,
  T ≠ ∞ — natCast fine; if the division bookkeeping fights, alternative:
  quantify L3/L4 with δ directly and conclude `≤ ∫VGo + T*δ` for ALL δ>0,
  then a final `iInf`/limit argument with `T*δ → 0` — the ε/T route is
  shorter. Conclude `LHS-inf ≤ ∫ VGo T 0 dγ₀ + ε`, then `le_iInf₂`.
- **L6 (sanity, optional).** T=1 instance recovers `bellman_value_eq`
  modulo definitional reshaping. Do NOT formalize as a theorem unless
  cheap (`example` with `rfl`-heavy proof); a comment suffices. The point
  of the campaign is T general, not re-deriving T=1.

Estimated size: definitions ~90 lines, L0–L5 ~300–400 lines, one file.
Compile strategy: `lake env lean BicausalOT/MultiPeriod.lean` per stage;
wire into Basic.lean + AxiomsAudit.lean (add `bellman_value_eq_multi`,
`MultiPeriod.VGo_le_costGo`, `MultiPeriod.exists_eps_strategy`) at the end.
KNOWN LEAN FRICTION to expect: (i) `PairHist (t+1)` must reduce to a
product for the pairing `(h, z)` — if elaboration balks, add
`@[simp] theorem pairHist_succ : PairHist X Y (t+1) = …` or use `show`;
(ii) recursive `theorem … | 0 | k+1` equation-style with IH inside
`lintegral_mono` — if the equation compiler resists, switch to
`induction k generalizing t h`; (iii) universe metavariables on
`PairHist : ℕ → Type _` — pin `Type (max u v)` if needed.

---

## §3. Phase 3: semianalyticity of value functions  [DONE 2026-07-10]

**Target (BS Prop 8.2 analogue):** X n, Y n Polish+Borel; κμ, κν Borel
Markov kernels; each `c t` lower semianalytic on `PairHist t` (with its
product Polish topology — note `PairHist` needs TopologicalSpace/Polish
instances by recursion here, unlike Phase 1). Then every
`VGo k t : PairHist t → ℝ≥0∞` is lower semianalytic.

Induction on k. k=0: `c t` lsa by hypothesis. Step: `VGo (k+1) t h =
c t h + inf_{γ ∈ Feas t h} ∫ VGo k (t+1) (h,z) dγ(z)`. Sum of lsa is lsa
(NEW LEMMA needed: `IsLowerSemianalytic.add` — via countable rational
decomposition `{f+g < c} = ⋃_{q} {f < q} ∩ {g < c − q}`-style; in ℝ≥0∞
use strict-below rationals; ~40 lines). For the inf term, the plan:

- Represent `Γ := {(h, γ) : γ ∈ Feas t h} ⊆ PairHist t × P(W)`,
  `W := X (t+1) × Y (t+1)`, `P(W) := ProbabilityMeasure W` with the weak
  topology. Then `h ↦ inf over the fiber Γ_h of F(h, γ)` where
  `F(h,γ) := ∫⁻ z, VGo k (t+1) (h,z) ∂γ`.
- `IsLowerSemianalytic.iInf_fiber` (BS 7.47, [DONE]) handles the fiber-inf
  given: (a) Γ analytic in the product, (b) F lsa on the product.
- (b) is `lintegral_lowerSemianalytic` (BS 7.48, [DONE]) applied to the
  **evaluation kernel** `κeval : PairHist t × P(W) → Measure W`,
  `κeval (h, γ) := γ`, composed with the lsa integrand
  `(h, γ, z) ↦ VGo k (t+1) (h, z)` (lsa via preimage under the continuous
  projection dropping γ — `AnalyticSet.preimage_of_continuous`). Needs
  7.48's hypotheses: κeval Borel-measurable and Markov. **[WALL? W2]**
  measurability of `γ ↦ γ` from Borel(weak topology on P(W)) to the Giry
  σ-algebra on Measure W — i.e. Borel(weak) ⊇ Giry. True on Polish spaces;
  proof route: evaluations against open sets are lsc in the weak topology
  (portmanteau) hence Borel; generate. Check recon: what Mathlib has.
- (a): Feas is cut out by two marginal equations. `γ ↦ γ.map fst`
  continuous P(W) → P(X) in weak topology (pushforward along continuous
  map — Mathlib `ProbabilityMeasure` should have continuity of map;
  projections are continuous). `h ↦ κμ t (projX t h)` is Borel (kernel
  Borel hypothesis + projX continuous/Borel — projX needs measurability:
  PairHist gets Borel instances in this phase). Then Γ = preimage of the
  diagonal under a Borel×continuous pair map; diagonal in P(X)×P(X) closed
  (weak topology Hausdorff — P(X) Polish **[WALL? W1]**) ⇒ Γ Borel ⇒
  analytic (`MeasurableSet.analyticSet`, ambient PairHist t × P(W) Polish
  — needs **W1** again for P(W) Polish).
- **W1: PolishSpace (ProbabilityMeasure W) for W Polish.** Mathlib has the
  Lévy–Prokhorov metric; check instance status (recon pending). If
  completeness/separability instances are missing this is a sub-campaign
  (Prokhorov's theorem territory) — reassess scope after recon; fallback:
  restrict Phase 3 statement to compact metric W (P(W) compact metrizable
  — easier) and note the general case as future work.
- **W2: Giry ⊆ Borel(weak).** Likely provable in ~100–200 lines via
  portmanteau lsc + `measurable_generateFrom`; recon will say how much is
  in Mathlib.
- Also needed: `IsLowerSemianalytic` currently lives on a TopologicalSpace
  variable; PairHist needs recursive TopologicalSpace + PolishSpace +
  BorelSpace instances (products preserve all three — instances by
  recursion like the MeasurableSpace plan; low risk).

Phase 3 verdict: genuinely valuable (it is THE theorem that justifies the
DST arsenal) but gated on W1/W2 recon. Do not start before Phase 2 is done.

---

## §3W. W1 sub-campaign: PolishSpace (ProbabilityMeasure Ω)  [DONE 2026-07-04]

**Recon verdict (2026-07-03, two agents): far better than feared.**
Mathlib ALREADY HAS: Prokhorov's theorem
`isCompact_closure_of_isTightMeasureSet`
(Mathlib/MeasureTheory/Measure/Prokhorov.lean:497, S. Gouëzel 2025),
`instCompactSpaceProbabilityMeasure`, `IsTightMeasureSet` +
`isTightMeasureSet_iff_exists_isCompact_measure_compl_le` +
`isTightMeasureSet_singleton` (single finite measure, completely-pseudo-
metrizable + 2nd-countable + Borel), RMK (Real + NNReal, regular),
Banach-Alaoglu, Stone-Weierstrass,
`LevyProkhorov.probabilityMeasureHomeomorph [SeparableSpace Ω]`,
`MetricSpace (LevyProkhorov (ProbabilityMeasure Ω)) [BorelSpace Ω]`,
`SeparableSpace.exists_measurable_partition_diam_le`, rich LP API
(one-sided `levyProkhorovDist_le_of_forall_le` for probability measures,
`left_measure_le_of_levyProkhorovEDist_lt`), thickening algebra,
`Metric.complete_of_cauchySeq_tendsto`,
`isCompact_of_totallyBounded_isClosed`,
`Topology.IsClosedEmbedding.polishSpace`.
MISSING (our targets): CompleteSpace / SeparableSpace / PolishSpace for
LevyProkhorov (ProbabilityMeasure Ω) or ProbabilityMeasure Ω.

Standing assumptions: `[MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
[MeasurableSpace Ω] [BorelSpace Ω]` (upgraded Polish; final wrapper takes
[PolishSpace Ω] and upgrades). New file:
`BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean`.

### Node A — LP-Cauchy sequences are uniformly tight  [attack first]

Target: `isTightMeasureSet_of_cauchySeq (u : ℕ → LevyProkhorov
(ProbabilityMeasure Ω)) (hu : CauchySeq u) : IsTightMeasureSet
{((u n).toMeasure : Measure Ω) | n : ℕ}`.

A1 (uniform finite ball cover): ∀ η δ > 0 (ℝ), ∃ F : Finset Ω, ∀ n,
(u n) ((⋃ x ∈ F, ball x η)ᶜ) ≤ δ-as-ℝ≥0∞.
Proof: (i) N from `Metric.cauchySeq_iff` at min(δ/2)(η/2). (ii) heads
i ≤ N: countable dense (x_i) covers Ω by (η/2)-balls; continuity from
below picks a finite subfamily of mass ≥ 1 − δ/2 per head; union the
finite sets. (iii) tails n ≥ N: B := ⋃_{x∈F} ball x (η/2), c :=
min(δ/2)(η/2): `left_measure_le_of_levyProkhorovEDist_lt` gives
(u N) B ≤ (u n)(thickening c B) + c; thickening c (ball x r) ⊆
ball x (r+c) and `thickening_biUnion` land in ⋃ ball x η; rearrange.
FRICTION: ProbabilityMeasure/Measure coercions; c both as ℝ (thickening
radius, via .toReal) and ℝ≥0∞ (edist bound, via ENNReal.ofReal).

A2 (assembly): ε > 0: A1 at (η, δ) = (2^{-j}, ε·2^{-(j+1)}) gives F_j;
K := ⋂_j ⋃_{x∈F_j} closedBall x (2^{-j}): closed, totally bounded
(j-th layer is a finite net), compact via
`isCompact_of_totallyBounded_isClosed`; μ_n(Kᶜ) ≤ Σ_j δ_j ≤ ε
(measure_iUnion_le + geometric sum). Conclude via
`isTightMeasureSet_iff_exists_isCompact_measure_compl_le`.

### Node B — separability of the LP space

Dense countable family: rational convex combinations of Diracs on a
countable dense D ⊆ Ω. Split:
B1: every μ is LP-close to a finitely-supported measure (real weights):
partition (A_n) from `SeparableSpace.exists_measurable_partition_diam_le`
(diam ≤ ε), finite N with mass 1 − ε, atoms x_n ∈ D within ε of A_n,
weights μ(A_n) (+ residual on x_0); one-sided estimate via
`levyProkhorovDist_le_of_forall_le`: A_n ∩ B ≠ ∅ ⇒ x_n ∈ thickening (3ε) B.
B2: same atoms, weight perturbation ≤ ε (rationalize weights): LP-dist
between discrete measures with common atoms ≤ total weight difference
(same one-sided criterion).
FRICTION: no ready constructor for finite Dirac mixtures as
ProbabilityMeasure — build `∑ i ∈ s, (w i) • Measure.dirac (x i)` and
prove IsProbabilityMeasure; ℝ≥0 vs ℝ≥0∞ weights; skip-empty-cells
bookkeeping.

### Node C — completeness and assembly

C1 `CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω))`:
`Metric.complete_of_cauchySeq_tendsto`; Node A ⇒ tight; Prokhorov
`isCompact_closure_of_isTightMeasureSet` (VERIFY exact instance context
at first use) ⇒ closure compact in weak topology;
`IsCompact.tendsto_subseq` (FirstCountable from PseudoMetrizable ✓) ⇒
weakly convergent subsequence; transfer to LP via
`probabilityMeasureHomeomorph`/`continuous_ofMeasure_probabilityMeasure`;
Cauchy + convergent subsequence ⇒ convergent (grep
`tendsto_nhds_of_cauchySeq_of_subseq`; else inline triangle).
C2 `PolishSpace (LevyProkhorov (ProbabilityMeasure Ω))`: metric + C1 +
(Node B ⇒ `UniformSpace.secondCountable_of_separable`).
C3 `PolishSpace (ProbabilityMeasure Ω')` for [PolishSpace Ω'][BorelSpace]:
upgrade, transfer C2 across the homeomorphism via
`Homeomorph.isClosedEmbedding` + `Topology.IsClosedEmbedding.polishSpace`.
Wire into Basic.lean + AxiomsAudit (A, B, C1, C3).

Attack order: A1 → A2 → C1 → B1 → B2 → C2 → C3 (completeness first —
biggest prize, self-contained; separability is independent grind).

---

## §4. Phase 4: ε-optimal measurable selection (BS 7.50 analogue)  [DONE 2026-07-10]

> **[DONE — read docs/design_phase4.md instead.]** The section below is
> the original reconnaissance; the delicate step it flags was resolved by
> the band-partition design (constant-threshold JvN + σ(Σ¹₁) domain
> bands). Delivered as `exists_eps_optimal_selector`
> (EpsOptimalSelection.lean, abstract BS 7.50) and
> `MultiPeriod.exists_eps_strategy_analyticallyMeasurable` +
> `MultiPeriod.bellman_value_eq_multi_measurable`
> (MeasurableStrategy.lean) — NOT the name `exists_eps_optimal_measurable_strategy`
> pencilled below.

Target: under Phase 3 hypotheses, for ε > 0 there is an
**analytically measurable** (σ(Σ¹₁)) ε-optimal transition family
`γε t : PairHist t → Measure W` — upgrading L3's arbitrary function.
Route: the set `Aε := {(h, γ) ∈ Γ : F(h,γ) ≤ VGo-inf-part h + ε}` is
analytic (Γ analytic ∩ sublevel-type set of lsa functions — the
comparison of two lsa functions needs care: use
`{(h,γ) : F(h,γ) < g(h) + ε}` with g lsa ⇒ countable rational union of
`{F < q} ∩ {q ≤ g + ε}`… the second set is co-analytic in general —
**CAUTION**, BS handle this with the "exact selection" machinery; the
clean statement: for lsa g, `{(h,γ) : F(h,γ) < q} ∩ (g-superlevel)` — needs
thought; BS 7.50's actual proof selects on `{F ≤ g + ε}` using that g is
the PARTIAL INFIMUM of F itself (so membership is expressible via F alone:
`Aε = {(h,γ) ∈ Γ : F(h,γ) < inf-fiber F h + ε}` and BS use a rational
layering over the VALUES of the inf — re-derive carefully at attack time;
this is the one genuinely delicate step of Phase 4). Then
`jankov_von_neumann` on Aε ⊆ PairHist t × P(W) (Polish, needs W1) gives a
σ(Σ¹₁)-measurable uniformizer; compose with κeval measurability (W2) to
land in `Measure W`. Deliverable: `exists_eps_optimal_measurable_strategy`.

---

## §4F. Phase 5: exact Borel-optimal strategies — the Feller/lsc model  [DONE 2026-07-12]

**Target (BS Ch. 8.3 lower-semicontinuous model, twin track to Phase 4):**
under STRONGER hypotheses — kernels Feller (weakly continuous in the
history) and stage costs lower semicontinuous — deliver STRICTLY stronger
conclusions: `VGo` genuinely **lsc** (not just lsa), the exact argmin
correspondence is nonempty/compact/weakly-measurable, and KRN
(`exists_measurable_selection`, in-repo) yields **exact Borel-measurable
optimal strategies** with `costGo = VGo` attained (ε = 0). Incomparable
with Phase 4 (neither dominates); mirrors BS's twin-track presentation.
Bonus deliverable en route: E3-D `exists_measurable_feasible_strategy`
(design_krn.md §4.2). Estimated ~950 lines over 4 files.

### 4F.1 Model primitives (settled design decisions)

- **ProbabilityMeasure-valued kernels as primitive.** Take
  `κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t+1))` (resp. κνP)
  as the data; Feller = `hκμ_cont : ∀ t, Continuous (κμP t)` (weak
  topology on P; no subtype-construction in hypotheses). The Phase-2/3/4
  theorems instantiate at the coerced kernels
  `κμ := fun t x => (κμP t x : Measure _)` with
  `hκμ_prob := fun t x => (κμP t x).2`-style instances.
- **Costs:** `hc_lsc : ∀ t, LowerSemicontinuous (c t)` on `PairHist t`
  (D1 topology instances).
- **σ-algebra hygiene (CRITICAL, checked):** KRN hit-sets must be Borel
  on `PairHist t`; the correspondence machinery lives in the WEAK
  topology on P. In the Feller model `h ↦ (μh, νh)` is CONTINUOUS, so
  everything transports; no Giry-vs-Borel(weak) gap. For the standalone
  Borel-model E3-D, Giry-measurability of the kernels is NOT enough
  (W2 gives Giry ⊆ Borel(weak), the wrong direction); E3-D therefore
  takes **WeakP-measurable kernels** as its honest hypothesis
  (`Measurable` into `WeakP _`), which Feller implies (continuous ⇒
  Borel). Do not attempt to derive it from Giry measurability — that is
  the open PR3 equality.

### 4F.2 File plan and lemma granularity

**File 1 `DescriptiveSetTheory/CouplingsUHC.lean`** (~220 lines) —
sequential upper hemicontinuity of the couplings correspondence
`Π : P(A) × P(B) → Set P(A × B)` (fixed, h-free; transport along
continuous/measurable `m` happens in the consumer files).
- U1 `tendsto_isTightMeasureSet`: a convergent sequence in
  `ProbabilityMeasure Ω` (Polish) is tight, `{γₙ} ∪ {γ}`. Via LP
  homeomorph + `isTightMeasureSet_of_cauchySeq` (convergent ⇒ Cauchy).
- U2 (E3-A) tight marginals ⇒ tight coupling union: reuse
  CouplingsCompact's slab bound `γ((K₁ ×ˢ K₂)ᶜ) ≤ μ K₁ᶜ + ν K₂ᶜ`
  (generalized from its tightness intermediates to families).
- U3 (sequential UHC core): `μₙ → μ`, `νₙ → ν`, `γₙ ∈ Π(μₙ, νₙ)` ⇒
  a subsequence `γ_{nₖ} → γ* ∈ Π(μ, ν)`. Proof: U1 marginals tight →
  U2 couplings tight → Prokhorov `isCompact_closure_of_isTightMeasureSet`
  + `IsCompact.tendsto_subseq` (metrizable by W1) → marginal maps
  continuous (`ProbabilityMeasure.continuous_map`) identify the limit.
- U4 (E3-B): for `C ⊆ P(A × B)` CLOSED, `{(μ,ν) | (Π(μ,ν) ∩ C).Nonempty}`
  is CLOSED (sequential closure in metrizable + U3).
- U5 (E3-C): for `U` OPEN, the hit-set is Borel: `U = ⋃ₙ Cₙ` (Fσ in
  metrizable, `Cₙ := {γ | (n+1)⁻¹ ≤ infDist γ Uᶜ}` or `IsClosed.isGδ`
  complement route) and hit-of-union = union-of-hits.

**File 2 `DescriptiveSetTheory/LscIntegral.lean`** (~200 lines) — joint
lower semicontinuity of the integral pairing.
- J0: extend `lowerSemicontinuous_lintegral_probabilityMeasure` to
  ∞-valued lsc integrands (if the in-repo statement carries an f ≠ ∞
  hypothesis — recon in flight): `∫⁻ f = ⨆ n, ∫⁻ min f n` (monotone
  convergence + `ennreal_iSup_min_natCast`), sup of lsc is lsc.
- J1 (THE new topological lemma): **joint continuity of the pairing**
  `(x, γ) ↦ γ.map (Prod.mk x) : H' × P(W) → P(H' × W)` (H', W Polish).
  Proof (sequential; metrizable both sides): use the portmanteau
  criterion "∀ open G, ν G ≤ liminf νₙ G ⇒ νₙ → ν". For open
  `G ⊆ H' × W` and `r < γ((mk x)⁻¹' G)`: inner regularity by compacts
  (finite Borel on Polish) gives compact `K ⊆ (mk x)⁻¹' G` with
  `γ K > r`; the finite-ball-cover tube argument on `{x} × K ⊆ G`
  produces OPEN `V ∋ x`, OPEN `O ⊇ K` with `V × O ⊆ G`; for n large
  `xₙ ∈ V` so `(mk xₙ)⁻¹' G ⊇ O`, and `liminf γₙ O ≥ γ O ≥ γ K > r`
  by the open portmanteau for `γₙ → γ`. NO tightness, NO equicontinuity.
- J2: for jointly lsc `f : H' × W → ℝ≥0∞`,
  `(x, γ) ↦ ∫⁻ z, f (x, z) ∂γ` is jointly lsc on `H' × P(W)`:
  `∫⁻ z, f (x, z) ∂γ = ∫⁻ p, f p ∂(γ.map (Prod.mk x))` (map along
  measurable `Prod.mk x`, integrand measurable since lsc), then
  (J0 functional, lsc on P(H' × W)) ∘ (J1 pairing, continuous) — an
  lsc-after-continuous composition.

**File 3 `LscBellman.lean`** (~400 lines) — the Feller model main line
(namespace MultiPeriod).
- FG1: `IsClosed (FeasGraph κμ κν t)` — equalizer of CONTINUOUS maps
  (κμP ∘ projX ∘ fst and γ ↦ γ.map fst, into T2 P-spaces); mirrors
  `measurableSet_feasGraph` with continuity replacing measurability.
- FG2: fibers `Feas(h)` compact + nonempty: instantiate
  `isCompact_probabilityMeasure_couplings` + F1 nonemptiness at the
  kernel marginals.
- B0 (attainment): an lsc `ℝ≥0∞`-valued function on a nonempty compact
  attains its infimum. If missing from Mathlib for lsc (recon), nested
  compact sublevel sets `{F ≤ Vinf + (n+1)⁻¹} ∩ Feas(h)` have the FIP.
- B1 (Berge min, parametrized by closed C ⊆ P(W)):
  `VminC F C h := ⨅ (γ : WeakP W) (_ : (h,γ) ∈ FeasGraph ∧ γ ∈ C), F (h, γ)`
  is **lsc in h** for jointly lsc F. Sequential: `hₙ → h` with
  `VminC hₙ < r`: minimizers `γₙ` exist (B0 on compact ∩ closed);
  marginals converge (Feller + `continuous_projX`); U3 extracts
  `γ* ∈ Feas(h) ∩ C`; joint lsc of F gives `F(h,γ*) ≤ liminf < r`.
  Handles empty fibers/∞ uniformly (iInf over ∅ = ∞). C := univ is the
  value case `Vinf`.
- V1 (VGo lsc, backward induction): `VGo c κμ κν k t` lsc on
  `PairHist t` for all k, t. Step: `VGo_succ_eq_weakP` reindex; the
  integrand `F_k(h,γ) := ∫⁻ z, VGo k (t+1) (h,z) ∂γ.toMeasure` is
  jointly lsc by J2 + IH (VGo k (t+1) lsc on PairHist (t+1) =
  PairHist t × W defeq); inf-part lsc by B1(univ); add `c t h` via
  lsc.add (`LowerSemicontinuous.add` — ℝ≥0∞ ContinuousAdd ✓, recon
  confirms name).
- M1 (argmin hit-sets against closed C):
  `Argmin(h) := {γ | (h,γ) ∈ FeasGraph ∧ F(h,γ) ≤ Vinf(h)}`. Key
  set identity (∞-band checked):
  `{h | (Argmin(h) ∩ C).Nonempty}
     = {h | (Feas(h) ∩ C).Nonempty} ∩ {h | VminC F C h ≤ Vinf h}`.
  (At `Vinf h = ∞` every feasible γ is optimal, RHS second factor is
  trivially true, first factor carries the content; at `Vinf h < ∞`
  attainment on the compact `Feas(h) ∩ C` converts the inequality into
  a minimizer in C.) First factor: closed by U4-transport (m continuous)
  — Borel ✓. Second: comparison of two lsc (hence Borel-measurable)
  functions — Borel ✓ (`measurableSet_le`).
- M2 (weak measurability + closed values): open U = ⋃ₙ Cₙ (U5);
  hit(Argmin, U) = ⋃ₙ hit(Argmin, Cₙ) (a minimizer in U lies in some
  Cₙ) — Borel. Values: nonempty (B0), compact (closed sublevel of the
  lsc F(h,·) ∩ compact Feas(h)).
- M3 (KRN per stage): `exists_measurable_selection` (Polish wrapper /
  metric upgrade on `WeakP W` — P Polish by W1) at Φ h := Argmin(h) at
  depth `T - t - 1` gives Borel-measurable `φ*ₜ : PairHist t → WeakP W`
  with exact optimality pointwise.
- M4 (assembly, horizon T): **`exists_optimal_measurable_strategy`** —
  `γ* : Strat X Y` with (i) feasibility, (ii) EXACT stage optimality at
  time-consistent depths, (iii) per-stage plain-Borel measurability
  (`Measurable (φ t : PairHist t → WeakP W)` — strictly stronger than
  Phase 4's σ(Σ¹₁)). Then the equality induction (ε = 0 analogue of
  L2+L4, cleaner as a direct `costGo = VGo` induction):
  **`costGo_eq_VGo_of_optimal`**: `t + k = T → costGo c γ* k t h = VGo c κμ κν k t h`,
  and the value-attainment corollary **`bellman_value_attained_measurable`**
  (the L5 strategy-infimum is ATTAINED by a Borel-measurable strategy).

**File 4 `MeasurableFeasibleStrategy.lean`** (E3-D bonus, ~120 lines) —
Borel model, WeakP-measurable kernels: KRN at Φ h := Feas(h) (closed ✓
compact ✓ nonempty by F1); hit-sets via U4/U5 + measurable m.
`exists_measurable_feasible_strategy`.

### 4F.3 Attack order

J0 → File 1 (U1–U5) → J1 → J2 → File 3 (FG → B → V1 → M1–M4) →
File 4 (bonus) → wire Basic + AxiomsAudit → docs. Compile per node with
`lake env lean`; full build per file. Adversarial design review BEFORE
File 3 (M1's ∞-band identity and J1's portmanteau argument are the
delicate steps this time).

### 4F.4 Phase-5 risk register (updated post-recon 2026-07-12, wf_51e58697)

| # | Risk | Impact | Status / Mitigation |
|---|---|---|---|
| P5-R1 | lsc-lintegral f ≠ ∞ hypothesis | J0 | **DISSOLVED**: `lowerSemicontinuous_lintegral_probabilityMeasure` (LintegralLsc.lean:138) has NO f≠∞ hypothesis (only the internal helper does). J0 dropped from the plan. |
| P5-R2 | portmanteau converse direction | J1 | **RESOLVED**: `MeasureTheory.tendsto_of_forall_isOpen_le_liminf'` (Portmanteau.lean:578, Measure-coercion form, [OpensMeasurableSpace] + countably-generated filter); forward direction `ProbabilityMeasure.le_liminf_measure_open_of_tendsto` (:323, [HasOuterApproxClosed]). Tube step: `generalized_tube_lemma` (Compact.lean:724) with `isCompact_singleton`. |
| P5-R3 | inner regularity by compacts | J1 | **RESOLVED**: instance `instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace` (RegularityCompacts.lean:190) fires for Polish+Borel, every measure; accessor `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`. |
| P5-R4 | lsc attainment on compact | B0 | **RESOLVED**: `LowerSemicontinuousOn.exists_isMinOn` (Semicontinuity/Basic.lean:77), only [LinearOrder β]; args (ne_s) (hs) (hf). |
| P5-R5 | M1 ∞-band set identity | M1 | RESOLVED in design (two-factor identity); verify adversarially before File 3 |
| P5-R6 | KRN has NO Polish wrapper; instance context | M3 | confirmed: `exists_measurable_selection` (MeasurableSelection.lean:243) wants [MetricSpace Y][SeparableSpace][CompleteSpace][BorelSpace], args (hne)(hclosed)(hmeas, inline `{a | (Φ a ∩ U).Nonempty}`); letI-upgrade `WeakP W` via `upgradeIsCompletelyMetrizable` (topology unchanged ⇒ Borel unchanged, §3W C3 pattern) |
| P5-R7 | Feller-as-subtype continuity awkward | all | κμP primitive (settled, §4F.1) |
| P5-R8 | joint-lsc integrand defeq PairHist (t+1) = PairHist t × W | V1 | same defeq-coherent instances that carried Phase 3/4 |
| P5-R9 | U1 "convergent ⇒ tight" route | U1 | `Filter.Tendsto.isCompact_insert_range`-style compact closure of range (verify name at compile; fallback: Tendsto.cauchySeq + LP transport per project isTightMeasureSet_of_cauchySeq), then Mathlib `isTightMeasureSet_of_isCompact_closure` (Tight.lean:215, needs letI PseudoMetricSpace upgrade on P) |

Confirmed name corrections vs the draft above: `LowerSemicontinuous.comp`
(NOT `.comp_continuous` — deprecated alias); `LowerSemicontinuous.add`
valid for ℝ≥0∞ (Basic.lean:511); `lowerSemicontinuous_iSup`
(CompleteLinearOrder); truncation via `.inf lowerSemicontinuous_const`;
`Metric.nhds_basis_ball`; FG2 bridge:
`isCompact_probabilityMeasure_couplings_toMeasure` (CouplingsCompact:170)
is already in the exact Measure.map shape of `Feas`;
`probabilityMeasure_map_eq_iff` (:51) converts. Sequential machinery:
`IsCompact.tendsto_subseq` (Sequences.lean:268, [FirstCountableTopology]),
`SeqContinuous.continuous` + instance chain PseudoMetrizable →
FirstCountable → FrechetUrysohn → Sequential (all priority-100 automatic),
`mem_closure_iff_seq_limit`.

## §5. Risk register

| Risk | Phase | Mitigation |
|---|---|---|
| W1: P(W) Polish missing in Mathlib | 3,4 | recon a89319…; fallback to compact W; or prove LP-completeness (big) |
| W2: Giry vs Borel(weak) | 3,4 | portmanteau route, prove ourselves if missing |
| L3 depth-consistency subtlety | 1–2 | design (a) fixed above — horizon-indexed strategy |
| PairHist defeq friction in patterns | 1–2 | `show`/simp lemmas `pairHist_succ` |
| ℝ≥0∞ arithmetic in L4/L5 (k*ε, ε/T) | 1–2 | all additions finite; avoid tsub; `ENNReal.mul_div_cancel'` |
| recursive instances (Phase 3 topologies) | 3 | mirror the MeasurableSpace recursion pattern |

## §6. Non-goals (explicitly out of scope for now)

- σ-finite/non-probability kernels; continuous time; W₂-adapted duality;
  Mathlib upstreaming (do AFTER the campaign, as a separate PR effort).

## §7. Battle log (append-only)

- **2026-07-03** Campaign opened. Arsenal §1 verified green (2447 jobs).
  Blueprint written. Recon agent dispatched for W1/W2 (LevyProkhorov /
  ProbabilityMeasure / Giry). Next action: scaffold
  `BicausalOT/MultiPeriod.lean` (D1–D8), compile, then L0–L2.
- **2026-07-03 (recon back, W1/W2 SCOUTED).** Mathlib status:
  LevyProkhorov type + Pseudo/MetricSpace instances EXIST
  (`Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean`);
  `eq_convergenceInDistribution` (LP topology = weak topology, needs
  [SeparableSpace Ω]) EXISTS; `MetrizableSpace (ProbabilityMeasure X)`
  EXISTS. **MISSING: CompleteSpace / SeparableSpace / SecondCountable /
  PolishSpace / StandardBorelSpace for ProbabilityMeasure or LevyProkhorov
  — W1 is a real wall (≈ Prokhorov theorem, major sub-campaign).**
  W2 (Giry ⊆ Borel(weak)): MISSING but provable ~150 lines: use
  `Measure.measurable_measure` criterion + portmanteau lsc of open-set
  evaluation (Portmanteau.lean has all directional lemmas) + Dynkin
  extension (complement via probability, countable disjoint unions).
  Useful confirmed API: `ProbabilityMeasure.map` + `continuous_map`,
  `Measure.measurable_coe/measurable_map/measurable_lintegral` (Giry side).
  Phase 3 re-scope decision deferred until Phase 2 is done; candidate
  fallbacks: (i) prove LP completeness+separability ourselves, (ii) compact
  one-step spaces variant.
- **2026-07-03 (PHASE 1-2 COMPLETE).** `BicausalOT/MultiPeriod.lean`
  (253 lines) green: D1-D8, L0 (`Feas.measure_univ`), L1
  (`VGo_le_pointwise`), L2 (`VGo_le_costGo`), L3 (`exists_eps_strategy` —
  simplification found during formalization: the horizon-consistent
  ε-optimality holds for ALL t without the `t < T` guard, no dite needed),
  L4 (`costGo_le_VGo_add`), L5 (`bellman_value_eq_multi`). Full build
  2448 jobs, 0 error / 0 warning; 24/24 axiom audits clean; wired into
  Basic.lean + AxiomsAudit.lean. Total compile-fix rounds: 5; errors all
  API-level (Strat explicit binders, defeq transparency of `le_refl` at
  k=0 → `le_of_eq rfl`, gcongr auto-descending into lintegral,
  `ENNReal.mul_div_cancel` signature). Design validated: nested-product
  histories + time-to-go recursion cost ZERO dependent-type friction.
  §2 status: [DONE]. Next front: Phase 3 (§3) — decide W1 strategy
  (LP completeness sub-campaign vs compact-space variant) before writing
  any Lean; update §3 with the decision first.
- **2026-07-03 (W1 GO — recon complete, sub-blueprint §3W written).**
  User ordered the LP-completeness assault. Recon: Prokhorov theorem
  FOUND in Mathlib (Prokhorov.lean, Gouëzel 2025) — campaign shrinks to
  ~600-700 lines: Node A (Cauchy⇒tight), Node B (separability via
  rational Dirac mixtures), Node C (assembly to
  `PolishSpace (ProbabilityMeasure Ω)`). Attack order A→C1→B→C2→C3.
  Next action: Node A in DescriptiveSetTheory/ProbabilityMeasurePolish.lean.
- **2026-07-03 (W1 Node A + C1 GREEN).** `ProbabilityMeasurePolish.lean`:
  `exists_range_measure_ball_compl_lt` (heads via
  `tendsto_measure_iInter_atTop`), `cauchySeq_exists_finset_measure_ball_compl_le`
  (A1; tail transfer via `right_measure_le_of_levyProkhorovEDist_lt`,
  thickening-of-complement trick avoids all ENNReal subtraction),
  `isTightMeasureSet_of_cauchySeq` (A2; K = ⋂ⱼ finite closed-ball unions,
  `TotallyBounded.isCompact_of_isClosed`, geometric tsum),
  `instance CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω))` (C1,
  via Prokhorov + `tendsto_nhds_of_cauchySeq_of_subseq`). 3 compile
  rounds. Node B (diracMix separability) + C2/C3 written, compiling now.
- **2026-07-04 (W1 WALL DOWN — §3W COMPLETE).**
  `ProbabilityMeasurePolish.lean` (632 lines) green: Node A
  (`isTightMeasureSet_of_cauchySeq`), C1
  (`instance CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω))`),
  Node B (`diracMix`, `le_diracMix_apply`,
  `exists_diracMix_levyProkhorovDist_le` — one-sided LP estimate via
  small-diameter measurable partitions, floor weights over common
  denominator m = ceil(N/eps)+1, no ENNReal subtraction anywhere),
  C2 (SeparableSpace + SecondCountable + PolishSpace instances for the
  LP space), C3 (`ProbabilityMeasure.instPolishSpace` via
  `probabilityMeasureHomeomorph.isClosedEmbedding.polishSpace`).
  Full build 2576 jobs, 0 error / 0 warning; 27/27 axiom audits clean.
  Total W1 compile-fix rounds: 6; all errors API-level (denseRange_iff
  argument order, add_le_add_right shape, Fin.sum_univ elaboration,
  field_simp leftover). LEAN LESSON recorded: this Mathlib's
  `add_le_add_right h c : c + a <= c + b` — prefer `add_le_add h le_rfl`.
  Phase 3 is now gated ONLY on W2 (Giry sigma-algebra vs Borel(weak) on
  P(W), recon-confirmed provable ~150 lines via portmanteau lsc +
  Dynkin/complement trick) plus the PairHist topology instances.
  Next action: W2 lemma (`measurable_toMeasure` : Borel(weak) to Giry)
  in a new section of ProbabilityMeasurePolish.lean or separate file,
  then Phase 3 semianalyticity per section 3 plan.
- **2026-07-04 (W2 DONE — Phase 3 fully unblocked).** New section in
  ProbabilityMeasurePolish.lean: `probabilityMeasure_continuous_lintegral`
  (test integrals continuous in weak topology, via testAgainstNN_coe_eq),
  `probabilityMeasure_borel_measurable_apply_isClosed` (closed sets, via
  HasOuterApproxClosed.apprSeq + measurable_of_tendsto_metrizable),
  `probabilityMeasure_borel_measurable_apply` (all Borel sets, pi-lambda
  induction with borel_eq_generateFrom_isClosed + isPiSystem_isClosed),
  `probabilityMeasure_borel_measurable_toMeasure` (**W2**: Borel(weak) to
  Giry). Full build 2576 jobs, 0/0; 30/30 audits clean. 2 compile rounds.
  LESSON: `Ω →ᵇ ℝ≥0` notation unavailable here — use
  `BoundedContinuousFunction Ω ℝ≥0`; lambda binders in set-equality RHS
  need explicit type ascriptions or the coercion retypes the binder.
  MULTI-AGENT ASSAULT LAUNCHED (workflow wf_b1daa031-2db) for Phase 3
  prerequisites: D1 PairHist topology instances, D2 IsLowerSemianalytic.add
  algebra, D3 Giry-valued equalizer measurability — each drafted by an
  agent, adversarially verified, then to be integrated by the main loop.
  Phase 3 main induction design (settled): reindex VGo inf over
  ProbabilityMeasure via L0; Γ Borel via D3 + W2 + Measure.measurable_map;
  integrand lsa via lintegral_lowerSemianalytic with evaluation kernel
  (h,γ) ↦ ↑γ (Measurable via W2 ∘ snd, Markov); fiber-inf via
  IsLowerSemianalytic.iInf_fiber; sum via D2. Type synonym decision:
  `WeakP W := ProbabilityMeasure W` with MeasurableSpace := borel(weak),
  BorelSpace ⟨rfl⟩, PolishSpace from W1.
- **2026-07-07 (quota incident + full relaunch).** First multi-agent
  launch (workflows wf_b1daa031-2db "phase3-assault" and wf_0fe1bdc6-caf
  "front-expansion", 19 agents total) died instantly on the session usage
  limit (reset 5:50am America/New_York). Probe at 05:52 EDT confirmed
  quota restored; BOTH workflows relaunched at full scale via
  resumeFromRunId. Fronts in flight: [assault] recon API, D1 PairHist
  topology instances, D2 IsLowerSemianalytic.add, D3 Giry equalizer, +3
  adversarial reviewers; [expansion] E1 Phase-3 main draft
  (SemianalyticBellman), E2 Phase-4 BS 7.50 design (band-gluing over
  rational levels of the inf), E3 KRN selection recon (possible upgrade:
  Feas fibers are weak-topology CLOSED, so KRN could give plain-Borel
  ε-optimal strategies, better than σ(Σ¹₁)), E4 redundant equalizer
  route, E5 README, E6 Mathlib PR plan, E7 T=1 bridge, +5 reviewers.
  Integration discipline: agents write ONLY to a staging area; the main loop
  is the single writer of repo files and runs final compiles.
- **2026-07-07 (WAVE 3 launched: wf_1997d83e-337 "hypothesis-elimination").**
  Strategic goal: turn the main theorems' hypotheses into theorems.
  F1 Feas/FeasibleSet₀/CouplingSet₀ nonemptiness via product couplings
  (kills h_Gamma_ne/hne hypotheses); F2 coupling sets CLOSED in weak
  topology (continuous marginal maps + T2); F3 coupling sets COMPACT
  (tight via marginal tightness + Prokhorov + F2) — together these
  upgrade Existence.lean from conditional to unconditional existence of
  optimal one-step plans (with F4); F4 lsc of γ ↦ ∫⁻ f dγ on P(W) for
  lsc f (layercake + Fatou + open-set portmanteau); F5 KRN measurable
  selection ADVANCE FORCE (full formalization attempt; key trick:
  keep approximate selectors countably-D-valued so test-set
  measurability reduces to fixed open sets; would give plain-Borel
  ε-optimal strategies via closed Feas fibers, upgrading Phase 4's
  σ(Σ¹₁) target); F6 abstract Choquet capacity design (Kechris 30.13
  general form; our recursion is already abstract in m — endgame axiom
  analysis via K ∩ Wₙ decreasing compacts). +5 adversarial reviewers.
  THREE workflows now in flight (~30 agents + grandchildren). Main loop
  remains sole repo writer; integration order on completion: interface
  lemmas (D1-D3, E4) → Phase-3 main (E1 skeleton) → hypothesis
  eliminations (F1-F4) → docs (E5/E6) → KRN/Phase-4 (F5/E2) next session.
- **2026-07-07 (battlefield salvage: equalizer INTEGRATED).** Agent E4
  completed `measurableSet_eq_measure` + `countable_generatePiSystem`
  before dying on quota; main loop verified (0/0/0) and integrated both
  into ProbabilityMeasurePolish.lean (new final section, own
  noncomputable section to dodge the Ω variables), added to AxiomsAudit.
  Phase-3 interface holes: equalizer DONE; D1 topology instances and D2
  lsa.add still owed by the relaunched wave 1. Salvaged artifacts also on
  disk: design_krn.md (E3 complete), draft_README.md (E5 complete,
  cached). All three workflows relaunched (ratchet strategy: workflow
  agent-cache makes progress monotone across quota windows). Full lake
  build deferred until workflows settle (concurrent scratch compiles).
- **2026-07-10 (RATCHET PAYOFF — all assault fronts complete).** Every
  drafting agent across the three waves finished (only reviewer agents
  lost to the next quota window; main loop re-verifies at integration).
  Integrated into repo (compile verification in flight):
  MultiPeriodTopology.lean (D1: recursive Topological/Polish/Measurable/
  Borel instances for PairHist/XHist/YHist, defeq-coherent products,
  projections continuous+measurable), DescriptiveSetTheory/LsaAlgebra.lean
  (D2: IsLowerSemianalytic.add [T2 only!], .const, .comp_continuous),
  FeasNonempty.lean (F1: product couplings ⇒ CouplingSet₀/FeasibleSet₀/
  Feas nonempty + hypothesis-free bellman_value_eq' and
  bellman_value_eq_multi'), DescriptiveSetTheory/CouplingsCompact.lean
  (F3: coupling sets tight + compact via Prokhorov),
  DescriptiveSetTheory/LintegralLsc.lean (F4: lsc of ∫⁻ f dγ in γ for lsc
  f≠∞, via ℝ-layercake + arbitrary-filter open portmanteau),
  DescriptiveSetTheory/MeasurableSelection.lean (F5: **Kuratowski–
  Ryll-Nardzewski measurable selection, fully proven, 255 lines** —
  namespace MeasurableSelection, exists_measurable_selection).
  Docs on disk: design_phase4.md (E2 — delicate step RESOLVED: JvN only
  on Γ ∩ {F < q} for constant rational q; domain partitioned by Nat.find
  bands of g incl. the co-analytic {g = ∞} piece — all in σ(Σ¹₁), the
  selection σ-algebra), design_krn.md (E3), design_mathlib_pr.md v2 (E6 —
  CORRECTION: this Mathlib pin ALREADY has a Giry-subtype MeasurableSpace
  instance on ProbabilityMeasure + Measurable.measure_of_isPiSystem_of_
  isProbabilityMeasure; proper PR3 target is a BorelSpace instance, i.e.
  σ-algebra EQUALITY Giry-subtype = Borel(weak) — we have ⊇ (W2); the
  reverse inclusion is an open TODO), draft_README.md v2 (E5 — flags:
  audit count now 32, BicausalOT/BicausalOT.lean is an unimported orphan
  with stale header), design_abstract_capacity.md (F6 — honest negative:
  naive abstract-capacity endgame FAILS, K₀∩W(β,n) fix does not
  lower-bound via capR; abstract version needs a different argument —
  parked). D3 GiryEq stronger variant (SecondCountable + one-sided
  finiteness) on disk as draft_GiryEq.lean — current integrated equalizer
  suffices for Phase 3; upgrade parked. NEXT: verify six-file compile,
  wire Basic+AxiomsAudit, full build, then Phase-3 main file (E1 died
  twice — main loop writes it solo from the settled design).
- **2026-07-10 (WAVE INTEGRATION COMPLETE — arsenal doubled).** Full
  build 8264 jobs, 0 errors / 0 warnings; **46/46 axiom audits clean**;
  0 sorry. Six agent-drafted files integrated and independently
  verified: MultiPeriodTopology.lean, DescriptiveSetTheory/
  {LsaAlgebra, CouplingsCompact, LintegralLsc, MeasurableSelection}.lean,
  FeasNonempty.lean. New headline theorems: `exists_measurable_selection`
  (Kuratowski-Ryll-Nardzewski, NOT in Mathlib),
  `isCompact_probabilityMeasure_couplings` + nonempty + closed,
  `lowerSemicontinuous_lintegral_probabilityMeasure`,
  `IsLowerSemianalytic.add/.const/.comp_continuous`,
  hypothesis-free `bellman_value_eq'` and
  `MultiPeriod.bellman_value_eq_multi'`, full PairHist
  Polish/Borel instance stack with measurable projections.
  TODO noted: slim the `import Mathlib` headers of the three F-files to
  targeted imports (build-time hygiene); consider the D3 stronger
  equalizer variant; BicausalOT/BicausalOT.lean orphan cleanup.
  REMAINING FRONTS: Phase-3 main theorem (VGo_isLowerSemianalytic — all
  interface pieces now green in-repo: instances, lsa.add, equalizer,
  W1/W2, 7.47, 7.48; main loop writes it solo per the settled §3+battle-
  log design), then Phase-4 per design_phase4.md (band-gluing selection,
  now upgradeable to plain-Borel via KRN since Feas fibers are
  weak-closed and isClosed_probabilityMeasure_couplings is in-repo).
- **2026-07-10 (PHASE 3 COMPLETE — the crown).**
  `BicausalOT/SemianalyticValue.lean` (~200 lines) green in 3 compile
  rounds: `WeakP` synonym (ProbabilityMeasure with Borel(weak) σ-algebra;
  NOTE: needed [OpensMeasurableSpace W] for the weak topology instance;
  the Polish instance transports via `ProbabilityMeasure.instPolishSpace
  (X := W)` — `inferInstanceAs` hit a kernel-level binder mismatch),
  `WeakP.measurable_toMeasure` (W2 packaged),
  `MultiPeriod.FeasGraph` + `measurableSet_feasGraph` (two Giry
  equalizers via `measurableSet_eq_measure` + `Measure.measurable_map` +
  W2∘snd and kernel∘projX∘fst), `VGo_succ_eq_weakP` (iInf reindex over
  probability measures, using L0), and the main induction
  `MultiPeriod.VGo_isLowerSemianalytic`: integrand lsa via
  `lintegral_lowerSemianalytic` with evaluation kernel (BS 7.48 — proved
  in THIS campaign), fiber-inf via `IsLowerSemianalytic.iInf_fiber`
  (BS 7.47 — the user's original library), sum via
  `IsLowerSemianalytic.add` (agent-drafted). Full build 8265 jobs, 0/0;
  **49/49 axiom audits clean**; 4418 Lean lines total. Every wall built
  for this theorem was used: Choquet capacitability → universal
  measurability → BS 7.48; LP completeness+separability → P(Ω) Polish
  (W1); Giry ⊆ Borel(weak) (W2); Giry equalizer; PairHist instances;
  LSA algebra. REMAINING FRONT: Phase 4 per design_phase4.md
  (band-gluing σ(Σ¹₁) selection; optional plain-Borel upgrade via the
  now-in-repo KRN `exists_measurable_selection` + weak-closed Feas
  fibers `isClosed_probabilityMeasure_couplings`). Cleanup TODOs: slim
  `import Mathlib` in F-files; copy design_phase4.md + design docs into
  repo (staged outside the repository — copy in before session loss);
  refresh README draft into repo root; orphan BicausalOT/BicausalOT.lean.
- **2026-07-10 (PHASE 4 COMPLETE — BS 7.50, campaign objective reached).**
  Two new files, both green, per docs/design_phase4.md:
  - `DescriptiveSetTheory/EpsOptimalSelection.lean` (238 lines, 3 compile
    rounds): `iInf_fiber_lt` (P4.1), `exists_fallback_selector` (P4.2),
    `exists_level_selector` (P4.3, dite-free by_cases with fallback arg),
    `AnalyticallyMeasurable.find` (P4.4 — Mathlib `Measurable.find`
    pinned at `analyticMeasurableSpace` via two `letI`, route 1 worked),
    `EpsOptimalSelection.bandPred/exists_band/band_lower_bound` (P4.5),
    **`exists_eps_optimal_selector`** (P4.6, the abstract BS 7.50
    ε-optimal half; band-gluing exactly as designed, band width ε' with
    no ε/2). Compile-fix rounds all syntax-level: `φ∞` is not a valid
    identifier (∞ is a token) → `φ₀`; `omit` for unused section vars;
    `rcases hfind :` already substitutes the scrutinee in the goal so
    the planned `rw [hfind]` was redundant.
  - `MeasurableStrategy.lean` (229 lines, **1 compile round**):
    `feasGraph_fiber_nonempty` (P4.8), `iInf_feas_eq_iInf_feasGraph`
    (P4.9, general integrand), `stageF_lowerSemianalytic` (P4.7c as a
    standalone theorem, replicating Phase 3's hintegrand block),
    **`exists_eps_strategy_analyticallyMeasurable`** (P4.11 — L3 upgraded:
    each stage factors through an `AnalyticallyMeasurable` map into
    `WeakP`), **`bellman_value_eq_multi_measurable`** (P4.12 — the
    strategy infimum restricts to stage-wise σ(Σ¹₁)-measurable
    strategies without changing the value; upper bound mirrors L5's
    ε/T argument with the measurable γε, lower bound inherited from L5).
  - Design deviations (both simplifications): P4.10 (Giry transport)
    OBSOLETE — Phase-3's `WeakP` synonym already packages W2 + the
    Polish upgrade, so the application is written directly against
    `FeasGraph`/`WeakP` (design's pinned names `GammaSet`/
    `VGo_lowerSemianalytic` landed as `FeasGraph`/`VGo_isLowerSemianalytic`);
    P4.12's `costGo_le_VGo_add_measurable` not stated separately since
    L4 consumes P4.11's clauses verbatim — the named value-equality
    corollary was formalized instead.
  - Full build 8267 jobs, 0 errors / 0 warnings; **56/56 axiom audits
    clean**; 0 sorry; 4900 Lean lines total. Adversarial review
    workflow wf_6e5344fc-34b (3 lenses: statement strength, proof
    soundness, integration/style) dispatched; findings to be triaged
    on completion. Every phase of the campaign (§2 Phases 1–2, §3W W1,
    W2, §3 Phase 3, §4 Phase 4) is now [DONE].
  REMAINING (post-campaign, optional): review-workflow findings triage;
  cleanup TODOs from 2026-07-10 entries (slim `import Mathlib` in
  F-files, README promotion, orphan BicausalOT/BicausalOT.lean, stale
  .cursor/rules + BicausalOT_proof.html); Mathlib upstreaming per
  docs/design_mathlib_pr.md; optional Phase-5 semicontinuous model
  (exact Borel selection) per design_krn.md §5.
- **2026-07-10 (Phase-4 adversarial review + dedup refactor).** Review
  workflow wf_6e5344fc-34b returned: proof-soundness CLEAN (0 findings),
  statement-strength CLEAN (1 traceability note: the P4.11/P4.12
  pointwise corollaries are verbatim applications, consciously not
  restated), integration-style 2 minor + 4 notes. Both minors fixed and
  re-verified: (i) `iInf_feas_eq_iInf_feasGraph` hoisted from
  MeasurableStrategy.lean into SemianalyticValue.lean;
  `VGo_succ_eq_weakP` now derives from it (`congr 1`) — the P4.9 "do not
  duplicate" order is honored; (ii) the evaluation-kernel BS 7.48 block
  factored as `MultiPeriod.lintegral_weakP_lowerSemianalytic`
  (SemianalyticValue.lean), consumed by both the Phase-3 induction step
  (with `ih (t+1)`) and Phase-4's `stageF_lowerSemianalytic` (now a thin
  wrapper). §4 body got a DONE-pointer to design_phase4.md with the
  final theorem names. Post-refactor: full build 8267 jobs 0/0, 56/56
  audits clean, 1 compile round. Notes accepted without action:
  namespace split defensible, `iInf_fiber_lt` no Mathlib duplicate,
  explicit `MeasurableSpace.Constructions` import matches house
  convention. CAMPAIGN CLOSED.
- **2026-07-12 (PHASE 5 COMPLETE — the Feller/lsc model, §4F).** Four
  new files, 967 lines, all green; full build 8271 jobs 0/0; **70/70
  axiom audits clean**; 5883 Lean lines total. Process: recon workflow
  (wf_51e58697, 3 agents — dissolved P5-R1/R2/R3/R4 before any Lean) →
  BLUEPRINT §4F design → adversarial design review (wf_8359bfcc, 2
  agents, both SOUND — simplified M1 to a split-free identity, routed
  B1 through sublevel-set sequential closedness, replaced the M4
  induction with `costGo_le_VGo_add` at ε := 0) → formalization.
  - `DescriptiveSetTheory/CouplingsUHC.lean` (206 lines, 3 rounds):
    U1 `isTightMeasureSet_range_of_tendsto` (convergent ⇒ tight via
    compact closure of range + Mathlib converse Prokhorov), U2
    `isTightMeasureSet_couplings_of_isTightMeasureSet` (slab bound), U3
    **`exists_tendsto_subseq_couplings`** (sequential upper
    hemicontinuity of the couplings correspondence), U4
    `isClosed_couplings_hit`, U5 `measurableSet_couplings_hit`
    (σ-algebra-POLYMORPHIC via `{m} + [BorelSpace]` binders — dodges the
    Giry trap) + `IsOpen.exists_iUnion_isClosed_of_pseudoMetrizable`
    (topology-level Fσ; Mathlib's name-clashing version is
    pseudo-emetric).
  - `DescriptiveSetTheory/LscIntegral.lean` (110 lines, 3 rounds — two
    were one missing `open scoped ENNReal`): J1
    **`continuous_probabilityMeasure_map_prodMk`** (joint continuity of
    `(x,γ) ↦ γ.map (Prod.mk x)`; converse portmanteau + inner
    regularity + tube lemma, no tightness), J2
    **`lowerSemicontinuous_lintegral_prodMk`** (jointly lsc integral
    pairing = lsc functional ∘ J1).
  - `LscBellman.lean` (438 lines, **2 rounds**): `WeakP.exists_measurable_selection`
    (KRN Polish wrapper), fiber compactness/nonemptiness bridges,
    `stageMin` + `VGo_succ_eq_stageMin`, B1
    **`lowerSemicontinuous_stageMin`** (Berge minimum, closed-constraint
    parametrized), V1 **`lowerSemicontinuous_VGo`** (BS 8.3 analogue),
    `argminSet` machinery (M1 `argminSet_hit_eq` two-factor identity —
    no ∞-split needed, M2 `measurableSet_argminSet_hit`), M4
    **`exists_optimal_measurable_strategy`** (exact ε = 0 optimality +
    plain-Borel stage measurability — strictly stronger than Phase 4's
    σ(Σ¹₁) under strictly stronger hypotheses),
    `costGo_eq_VGo_of_optimal` (le_antisymm of L2 and L4 at ε := 0),
    **`bellman_value_attained_measurable`** (the Bellman value is a
    MINIMUM, attained by a Borel-measurable strategy, pointwise in h₀).
  - `MeasurableFeasibleStrategy.lean` (E3-D, 152 lines, 3 rounds):
    **`exists_measurable_feasible_strategy`** — measurable bicausal
    Markov strategies exist in the plain Borel model under weak-Borel
    measurable kernels (honest hypothesis; Giry measurability would not
    suffice — open PR3 direction).
  - LEAN LESSONS recorded: (i) `φ∞` is not an identifier; (ii)
    `rcases h :` substitutes the scrutinee — follow-up `rw [h]` is
    redundant; (iii) WeakP has NO coe to Measure — use `.toMeasure`;
    (iv) **R2 trap is real**: a pair-of-ascriptions lambda
    `fun h => ((a : WeakP _), (b : WeakP _))` can COLLAPSE to
    ProbabilityMeasure/Giry during `have`-elaboration — pin codomain
    σ-algebras with `@Measurable` in statements about WeakP-valued maps;
    (v) `push_neg` deprecated → `not_exists.mp`; (vi) self-recursion
    from an unqualified name inside a same-named wrapper — qualify
    `_root_.`.
  REMAINING (post-campaign): Phase-5 code review triage; the cleanup
  backlog (2026-07-10 entries + repo hygiene: git init/PDF ignore,
  README promotion, orphan/stale files); Mathlib upstreaming
  (design_mathlib_pr.md — now also KRN, U3/J1, P(Ω) Polish); optional:
  γ₀-side attainment (CouplingSet₀ compact + J-machinery, noted by the
  design review as nearly free).
- **2026-07-12 (Phase-5 adversarial review — triage).** Workflow
  wf_a56bae71 (3 lenses): **statement-strength CLEAN** (all six attack
  angles verified — exactness, no Giry capture in the final statements,
  σ-algebra-polymorphic U5 safety argument holds, E3-D hypothesis is
  honestly weak-Borel), **proof-soundness CLEAN** (every proof
  independently re-derived: J1 portmanteau, U1/U3 identification, B1
  sublevel route, V1 identification, M1 ∞-band, M4/ε=0 closures),
  integration-style 5 minor + 4 notes. Fixed now: +5 audits
  (U2, argminSet_nonempty/isClosed/hit_eq, E3-D hit lemma) → **75/75
  clean**, full build 8271 jobs 0/0; battle-log line-count erratum
  (actual: CouplingsUHC 220, LscIntegral 102, LscBellman 504,
  MeasurableFeasibleStrategy 141); FG1 (global FeasGraph closedness)
  consciously DROPPED — per-fiber compactness + U4-transported
  hit-sets replace it, nothing needs the global statement. PARKED for
  the next cleanup session (review findings, no correctness impact):
  (i) extract a shared "closed-target hit-sets are Borel for weak-Borel
  measurable kernels" core in LscBellman, subsuming the Feller version
  (Continuous.measurable) and E3-D's per-Cₙ piece, killing the
  duplicated ~20-line hset transport identity; (ii) a generic
  hit-of-union helper next to the Fσ lemma (3 inline copies, ~35
  lines); (iii) optionally factor the thrice-repeated attainment block
  in LscBellman into a "stageMin is attained" lemma; (iv) relocate
  feasGraph_fiber_nonempty from MeasurableStrategy.lean to
  SemianalyticValue.lean so LscBellman need not import the Phase-4
  file; (v) γ₀-side attainment (outer infimum over initial couplings —
  lsc of ∫VGo dγ₀ + CouplingSet₀ compact, both in-repo) as a natural
  capstone lemma. CAMPAIGN CLOSED — six phases, all [DONE].
