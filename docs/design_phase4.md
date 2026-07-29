# FRONT E2 — Phase 4 design: ε-optimal analytically-measurable selection (BS 7.50 analogue)

Date: 2026-07-07; re-verified 2026-07-10 (second independent adversarial
pass, §4.1 — all signatures re-checked against source, two stale line
citations fixed, one instance pin added as R11).
Status: COMPLETE mathematical design at formalization
granularity. No Lean written; every lemma below carries a Lean-like
signature checked against the exact statements in the repository
(`Tree.lean` JvN, `LowerSemianalytic.lean` 7.47, `KernelIntegral.lean` 7.48,
`ProbabilityMeasurePolish.lean` W1/W2, `MultiPeriod.lean` L0–L5).

**Deliverable:** `exists_eps_strategy_analyticallyMeasurable` — under the
Phase-3 hypotheses, for every `ε > 0` and horizon `T` there is a strategy
`γε : Strat X Y` that is pointwise feasible, stage-wise ε-optimal at the
time-consistent depth `T − t − 1` (exactly mirroring
`MultiPeriod.exists_eps_strategy`), and **σ(Σ¹₁)-measurable** at every
stage (each `γε t` factors through an `AnalyticallyMeasurable` map into
`ProbabilityMeasure W`).

---

## §0. Interfaces consumed (all named against actual repo statements)

Arsenal (already green):

- `jankov_von_neumann (P : Set (X × Y)) (hP : AnalyticSet P) (hne : P.Nonempty) :
   ∃ φ : X → Y, AnalyticallyMeasurable φ ∧ ∀ x ∈ Prod.fst '' P, (x, φ x) ∈ P`
  — Tree.lean:284; `X Y` Polish. NOTE the two preconditions: `P` analytic
  AND `P.Nonempty`; the uniformization property holds only on `Prod.fst '' P`.
- `IsLowerSemianalytic.iInf_fiber (hD : AnalyticSet D) (hf : IsLowerSemianalytic f) :
   IsLowerSemianalytic (fun x => ⨅ y (_ : (x, y) ∈ D), f (x, y))`
  — LowerSemianalytic.lean:35 (BS 7.47); needs `[PolishSpace X] [PolishSpace Y] [T2Space X]`.
- `IsLowerSemianalytic f : ∀ c : ℝ≥0∞, AnalyticSet {x | f x < c}` — note `c`
  ranges over ALL of `ℝ≥0∞` including `⊤`; we use `c = ⊤` below.
- `AnalyticSet.inter'` (KernelIntegral.lean:32, needs `[T2Space]` ambient),
  `MeasurableSet.analyticSet`, `AnalyticSet.mem_analyticMeasurableSpace`,
  `AnalyticSet.compl_mem_analyticMeasurableSpace` (AnalyticSigmaAlgebra.lean).
- `lintegral_lowerSemianalytic` (KernelIntegral.lean:283, BS 7.48).
- W1: `ProbabilityMeasure.instPolishSpace` (ProbabilityMeasurePolish.lean:626).
- W2: `probabilityMeasure_borel_measurable_toMeasure :
   @Measurable (ProbabilityMeasure Ω) (Measure Ω) (borel _) inferInstance (↑)`
  (ProbabilityMeasurePolish.lean:718; standing vars `[MetricSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]`, Separable/Complete omitted via `omit`).
- Phase 2: `Feas`, `Strat`, `VGo`, `Feas.measure_univ` (L0),
  `exists_eps_strategy` (L3 — the statement we upgrade),
  `costGo_le_VGo_add` (L4 — consumed verbatim by the corollary P4.12).
- Mathlib: `Measurable.find` (`MeasureTheory/MeasurableSpace/Constructions.lean:507`,
  recon-confirmed in design_krn.md §1.2):
  `(hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet {x | p n x})
   (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x`
  — crucially the DOMAIN σ-algebra is an arbitrary `[MeasurableSpace α]`,
  so it instantiates at `analyticMeasurableSpace H`.

Phase-3 outputs assumed (interface pinned in §3, lemma P4.7; Phase 4's
application half is written against these three statements and nothing else
from Phase 3, so the abstract half §2 can be formalized IMMEDIATELY,
before Phase 3 lands).

Throughout, `W t := X (t+1) × Y (t+1)` and `P(W) := ProbabilityMeasure (W t)`
with the weak topology (Polish by W1), and `H t := PairHist X Y t` with the
Phase-3 recursive Polish/Borel instances (D1).

---

## §1. The delicate step, and its resolution

### 1.1 The problem

Fix a stage `t` and depth `k`. Phase 3 provides, on the product
`H × P(W)` (Polish):

- `Γ := GammaSet t` — the feasibility graph, Borel hence **analytic**;
- `F (h, γ) := ∫⁻ z, VGo c κμ κν k (t+1) (h, z) ∂(γ : Measure W)` — **lsa**
  (BS 7.48 via the evaluation kernel);
- `g h := ⨅ γ (_ : (h,γ) ∈ Γ), F (h, γ)` — **lsa** (BS 7.47).

We want a σ(Σ¹₁)-measurable `φ` with `(h, φ h) ∈ Γ` and
`F (h, φ h) ≤ g h + ε` for all `h`. The tempting move — apply JvN to

```
Aε := {(h, γ) ∈ Γ | F (h, γ) < g h + ε}
```

— is BLOCKED: `Aε` mixes the lsa function `F` from **below** (sublevels of
`F` are analytic ✓) with the lsa function `g` from **above** (we need
`g h + ε` to MAJORIZE `F`, i.e. superlevel information about `g`; superlevels
of an lsa function are only **co-analytic**). Concretely, the natural
rational decomposition

```
{F < g∘fst + ε} = ⋃_{q} ({F < q} ∩ {q ≤ g∘fst + ε})
```

has analytic left factors but co-analytic right factors; the union is in
σ(Σ¹₁) but NOT analytic, and `jankov_von_neumann` requires an *analytic*
set. Re-expressing `g` through `F` (`q ≤ g + ε` iff `∀ γ', F(h,γ') > q − ε`)
just reproduces a universal quantifier over the fiber — co-analytic again.
There is no fix that makes a single analytic selection set: in the Borel
model, Borel/analytic ε-optimal selection genuinely fails
(Blackwell-type counterexamples; see design_krn.md §4.1), so any correct
proof MUST spend σ(Σ¹₁)-measurability somewhere.

### 1.2 The Bertsekas–Shreve resolution (7.50), worked out exactly

Spend the σ(Σ¹₁) budget on the *domain partition*, not on the selection
sets:

1. **Never compare `F` with `g` inside a selection set.** Only ever select
   on `A q := Γ ∩ {F < q}` for **constant** thresholds `q` — this is
   analytic (analytic ∩ analytic, `AnalyticSet.inter'`), so JvN applies.
2. **Steer which threshold to use by the VALUE of `g`,** via a countable
   partition of `H` into "bands". Both sublevels `{g < c}` (analytic) and
   superlevels `{g ≥ c}` (co-analytic) lie in **σ(Σ¹₁)** — the selection
   σ-algebra is σ(Σ¹₁), not the analytic sets, so bands
   `{c₁ ≤ g < c₂} = {g < c₂} ∩ {g < c₁}ᶜ` are measurable FOR FREE at the
   σ-algebra level. This is the precise sense of the blueprint CAUTION's
   hint: the co-analytic half is absorbed by σ(Σ¹₁), never fed to JvN.
3. **Glue** the countably many JvN selectors (one per band) plus one
   fallback selector (for the `g = ∞` band) with a countable piecewise
   lemma — which at the σ-algebra level is literally Mathlib's
   `Measurable.find` instantiated at `analyticMeasurableSpace H`.

**Constants, nailed.** Let `ε' := min ε 1` (so `0 < ε' ≤ ε`, `ε' ≤ 1 < ∞`;
this makes all band arithmetic finite even when `ε = ∞`). Grid: multiples
`m • ε'` for `m : ℕ`. Effective bands (realized through `Nat.find`, see
P4.5–P4.6):

```
B∞    := {h | g h = ∞}                       (fallback band)
B m   := {h | m·ε' ≤ g h < (m+1)·ε'},  m = 0, 1, 2, …
```

Selector on `B m`: JvN uniformizer of `A ((m+1)·ε') = Γ ∩ {F < (m+1)·ε'}`.

- *Coverage / fiber-nonemptiness:* for `h ∈ B m`, `g h < (m+1)·ε'` and `g`
  is the fiber-infimum of `F`, so `∃ γ` in the fiber with
  `F (h,γ) < (m+1)·ε'` (inf-approximation, `iInf_lt_iff`); hence
  `h ∈ Prod.fst '' A ((m+1)·ε')` and the JvN uniformization property
  applies AT `h`.
- *Optimality:* the selected `γ = φ h` satisfies
  `F (h, φ h) < (m+1)·ε' = m·ε' + ε' ≤ g h + ε' ≤ g h + ε`,
  using the band's LOWER edge `m·ε' ≤ g h`. **Band width `ε'` suffices —
  no `ε/2` is needed** — because the selection threshold is the band's
  *upper* edge while `g` is bounded below by the band's *lower* edge; the
  total slack is exactly one band width. (BS's proof does the same with a
  partition `{q_i ≤ g < q_i + ε}`; the `ε/2` in the front-prompt hint is a
  safety margin that turns out to be unnecessary.)
- *`g h = ∞` band:* EVERY feasible `γ` is ε-optimal there
  (`F ≤ ∞ = g h ≤ g h + ε`), so use one JvN uniformizer `φ∞` of `Γ`
  itself (analytic; nonempty as soon as `H` is nonempty, by
  fiber-nonemptiness).
- All arithmetic is in `ℝ≥0∞` with additions and one `Nat`-cast
  multiplication; **no subtraction anywhere**.

The whole construction is packaged as ONE abstract theorem (P4.6) about a
Polish pair `(H, E)`, an analytic `Γ ⊆ H × E` with nonempty fibers, and an
lsa `F` — BS Prop 7.50 (ε-optimal half) in `ℝ≥0∞`. The OT application then
only instantiates.

---

## §2. Abstract half — new file `BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean`

Standing variables for §2:

```lean
variable {H E : Type*} [TopologicalSpace H] [PolishSpace H]
  [TopologicalSpace E] [PolishSpace E]
variable {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
```

Notation (local abbreviation in proofs, not a def):
`g : H → ℝ≥0∞ := fun h => ⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)`.

### P4.1 (fiber inf-approximation)

```lean
theorem iInf_fiber_lt {h : H} {q : ℝ≥0∞}
    (hlt : (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) < q) :
    ∃ e : E, (h, e) ∈ Γ ∧ F (h, e) < q
```

*Proof.* `iInf_lt_iff` twice (complete-lattice `ℝ≥0∞`), exactly as in the
forward direction of `IsLowerSemianalytic.iInf_fiber`'s `h_sub`
(LowerSemianalytic.lean:47–51). 3 lines. Conversely (used in P4.9 only via
`iInf₂_le`, no lemma needed).

### P4.2 (fallback selector on the full graph)

```lean
theorem exists_fallback_selector (hΓ : AnalyticSet Γ) (hΓne : Γ.Nonempty)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ ∀ h, (h, φ h) ∈ Γ
```

*Proof.* `jankov_von_neumann Γ hΓ hΓne` gives `φ` with the uniformization
property on `Prod.fst '' Γ`; for any `h`, `hfib h = ⟨e, he⟩` gives
`h ∈ Prod.fst '' Γ` via `⟨(h, e), he, rfl⟩`. 5 lines. (This is already the
`ε = ∞`/`g = ∞` case in full; it is also independently quotable as
"a σ(Σ¹₁)-measurable feasible selector exists".)

### P4.3 (level selectors — one per constant threshold)

```lean
theorem exists_level_selector (hΓ : AnalyticSet Γ)
    (hF : IsLowerSemianalytic (X := H × E) F)
    (φ∞ : H → E) (hφ∞ : AnalyticallyMeasurable φ∞) (q : ℝ≥0∞) :
    ∃ χ : H → E, AnalyticallyMeasurable χ ∧
      ∀ h : H, (∃ e, (h, e) ∈ Γ ∧ F (h, e) < q) →
        (h, χ h) ∈ Γ ∧ F (h, χ h) < q
```

*Proof.* Set `A := Γ ∩ {p | F p < q}`; `hA : AnalyticSet A :=
hΓ.inter' (hF q)` (ambient `H × E` is Polish hence T2). Case split:

- `hAne : A.Nonempty`: `jankov_von_neumann A hA hAne` gives `χ`; for `h`
  with hypothesis `⟨e, heΓ, heF⟩`, `h ∈ Prod.fst '' A` via
  `⟨(h,e), ⟨heΓ, heF⟩, rfl⟩`, so `(h, χ h) ∈ A`, i.e. both conclusions.
- `¬A.Nonempty`: the hypothesis `∃ e, …` is false for every `h`
  (a witness would populate `A`), so the ∀-statement is vacuous; return
  `χ := φ∞`. ~15 lines.

(Design note: passing the fallback `φ∞` as an argument avoids needing
`Γ.Nonempty`/`Nonempty E` inside this lemma and keeps it usable at `q = 0`,
where `A = ∅` because `¬(x < 0)` in `ℝ≥0∞`.)

### P4.4 (THE GLUE LEMMA — countable σ(Σ¹₁)-piecewise gluing)

The prompt-requested lemma, in the `Nat.find` form that is directly
Lean-implementable:

```lean
theorem AnalyticallyMeasurable.find
    {ψ : ℕ → H → E} (hψ : ∀ m, AnalyticallyMeasurable (ψ m))
    {p : ℕ → H → Prop} [∀ m, DecidablePred (p m)]
    (hp : ∀ m, @MeasurableSet H (analyticMeasurableSpace H) {h | p m h})
    (hex : ∀ h, ∃ m, p m h) :
    AnalyticallyMeasurable (fun h => ψ (Nat.find (hex h)) h)
```

*Proof (route 1, preferred).* `AnalyticallyMeasurable` unfolds to
`@Measurable H E (analyticMeasurableSpace H) (borel E)`; apply Mathlib's
`Measurable.find` with the domain instance pinned to
`analyticMeasurableSpace H` (it is σ-algebra-polymorphic in the domain,
recon-confirmed). 3 lines + instance pinning (`letI`).

*Proof (route 2, fallback if `Measurable.find`'s exact shape fights).* For
`B` Borel in `E`:
`(fun h => ψ (Nat.find (hex h)) h) ⁻¹' B
  = ⋃ m, ({h | Nat.find (hex h) = m} ∩ (ψ m) ⁻¹' B)`,
and `{h | Nat.find (hex h) = m} = {h | p m h} ∩ ⋂ j < m, {h | p j h}ᶜ`
(`Nat.find_eq_iff`) — a finite intersection of σ(Σ¹₁) sets and complements,
so the union is σ(Σ¹₁). ~15 lines.

*Documentation remark (partition form).* The classical statement "a
piecewise definition over a countable σ(Σ¹₁)-partition
`H = ⨆ m, S m` with analytically-measurable pieces `ψ m` is analytically
measurable" is the special case `p m h := h ∈ S m` (any measurable
choice-of-index works since `Nat.find` picks the least; disjointness is
NOT needed, only coverage). We do not formalize the partition form
separately — the `find` form is strictly more convenient and is what P4.6
uses. The binary case is Mathlib's `Measurable.piecewise`, also
σ-algebra-polymorphic, available if ever needed.

### P4.5 (band bookkeeping in `ℝ≥0∞`)

Two micro-lemmas, both pure `ℝ≥0∞` arithmetic. Fix `ε' : ℝ≥0∞` with
`hε'0 : 0 < ε'` and `hε'top : ε' ≠ ∞`, and an arbitrary `v : ℝ≥0∞`
(instantiated at `v := g h`). Define

```lean
-- the band predicate (p 0 = infinite band; p (m+1) = value below (m+1)·ε')
p : ℕ → ℝ≥0∞ → Prop
p 0     v := v = ∞
p (m+1) v := v < ((m + 1 : ℕ) : ℝ≥0∞) * ε'
```

```lean
theorem exists_band (v : ℝ≥0∞) : ∃ m : ℕ, p m v
```

*Proof.* If `v = ∞`, take `m = 0`. Else `v ≠ ∞`; `v / ε' ≠ ∞`
(`ENNReal.div_eq_top`: needs `ε' ≠ 0` and `v ≠ ∞` — both hold);
`ENNReal.exists_nat_gt` gives `n` with `v / ε' < n`; then `v < n * ε'` by
`ENNReal.div_lt_iff` (hypotheses `ε' ≠ 0 ∨ _`, `ε' ≠ ∞ ∨ _` — satisfied);
`n ≠ 0` (else `v < 0`), write `n = m + 1`. ~12 lines.

```lean
theorem band_lower_bound {v : ℝ≥0∞} {m : ℕ}
    (hmin : ∀ j < m + 1, ¬ p j v) --  i.e. Nat.find = m+1 minimality
    : ((m : ℕ) : ℝ≥0∞) * ε' ≤ v
```

*Proof.* Cases on `m`. `m = 0`: `0 * ε' = 0 ≤ v`. `m = j+1`:
`hmin (j+1) (by omega)` gives `¬(v < (j+1)·ε')`, i.e. `(j+1)·ε' ≤ v` by
`not_lt`. ~6 lines. (In the main proof this is invoked with
`hmin := fun j hj => Nat.find_min (hex h) (by omega)`-style; stated here
with the explicit minimality hypothesis to stay `Nat.find`-agnostic.)

Also the one-liner used in the final chain:
`((m + 1 : ℕ) : ℝ≥0∞) * ε' = ((m : ℕ) : ℝ≥0∞) * ε' + ε'`
(`push_cast; ring` or `Nat.cast_succ, add_mul, one_mul`). Inline, no lemma.

### P4.6 (ABSTRACT MAIN — BS Prop 7.50, ε-optimal half, `ℝ≥0∞` version)

```lean
/-- **ε-optimal analytically measurable selection** (Bertsekas–Shreve,
Prop 7.50 analogue). If `Γ ⊆ H × E` is analytic with nonempty fibers and
`F` is lower semianalytic, then for every `ε > 0` there is a
σ(Σ¹₁)-measurable selector that is everywhere feasible and everywhere
ε-optimal for the fiber infimum. -/
theorem exists_eps_optimal_selector
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ (∀ h, (h, φ h) ∈ Γ) ∧
      ∀ h, F (h, φ h) ≤ (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) + ε
```

*Proof (complete).*

**Step 0 (degenerate domain).** `rcases isEmpty_or_nonempty H`. If `H` is
empty: `φ := fun h => isEmptyElim h`; `AnalyticallyMeasurable φ` holds
because every `Set H` equals `∅` (`Set.eq_empty_of_isEmpty`), hence every
preimage is measurable; the two ∀-clauses are vacuous. Assume `Nonempty H`
henceforth; then `Γ.Nonempty` (pick `h₀`, apply `hfib h₀`).

**Step 1 (normalize ε).** `ε' := min ε 1`. `hε'0 : 0 < ε'`
(`lt_min hε zero_lt_one`), `hε'top : ε' ≠ ∞` (`≤ 1`), `hε'ε : ε' ≤ ε`
(`min_le_left`). All bands are built from `ε'`; the conclusion weakens to
`ε` only in the last line.

**Step 2 (semianalyticity of `g`).**
`hg : IsLowerSemianalytic g := hF.iInf_fiber hΓ` — instances: `H`, `E`
Polish ✓, `T2Space H` from Polish (metrizable) ✓. This is the ONLY fact
about `g` used; in particular `{g < c}` is analytic for every
`c : ℝ≥0∞` including `c = ⊤`.

**Step 3 (selector family).** `φ∞` from P4.2 (`hΓ`, `Γ.Nonempty`, `hfib`).
For `m : ℕ` let `χ m` be the P4.3 selector at threshold
`q m := (m : ℝ≥0∞) * ε'` (fallback argument `φ∞`). Define
`ψ : ℕ → H → E` by `ψ 0 := φ∞` and `ψ (m+1) := χ (m+1)`.
Each `ψ m` is `AnalyticallyMeasurable` ✓. (Equivalently `ψ m := χ m` for
all `m` also works — `χ 0` degenerates to `φ∞` because
`A 0 = Γ ∩ {F < 0} = ∅`; the explicit split by `m` is clearer to read and
to prove against.)

**Step 4 (band predicate and its σ(Σ¹₁)-measurability).**
`p m h := P4.5-p m (g h)`, i.e. `p 0 h := (g h = ∞)`,
`p (m+1) h := g h < ((m+1 : ℕ) : ℝ≥0∞) * ε'`. Then

- `{h | p 0 h} = {h | g h < ⊤}ᶜ` (ext; `lt_top_iff_ne_top`, `not_not`) —
  complement of an analytic set (`hg ⊤`), in σ(Σ¹₁) by
  `AnalyticSet.compl_mem_analyticMeasurableSpace`.
- `{h | p (m+1) h}` is analytic (`hg _`), in σ(Σ¹₁) by
  `AnalyticSet.mem_analyticMeasurableSpace`.
- `hex : ∀ h, ∃ m, p m h := fun h => exists_band (g h)` (P4.5).

**Step 5 (glued selector).** `φ := fun h => ψ (Nat.find (hex h)) h`;
`AnalyticallyMeasurable φ` by P4.4 (`hψ`, `hp`, `hex`).

**Step 6 (feasibility + ε'-optimality, case split on `m₀ := Nat.find (hex h)`).**

*Case `m₀ = 0`.* `Nat.find_spec` gives `g h = ∞`. `φ h = φ∞ h`, so
`(h, φ h) ∈ Γ` by P4.2 ✓, and
`F (h, φ h) ≤ ⊤ = g h ≤ g h + ε'` (`le_top`, then rewrite) ✓.

*Case `m₀ = m + 1`.* `Nat.find_spec` gives
`g h < ((m+1 : ℕ) : ℝ≥0∞) * ε'`. By P4.1 there is `e` with `(h, e) ∈ Γ`
and `F (h, e) < (m+1)·ε'` — this is exactly the hypothesis of P4.3's
∀-clause for `χ (m+1)` at `h`, so
`(h, φ h) ∈ Γ` ✓ and `F (h, φ h) < (m+1)·ε'`.
Minimality `Nat.find_min` gives `∀ j < m+1, ¬ p j h`; P4.5
`band_lower_bound` yields `(m : ℝ≥0∞) * ε' ≤ g h`. Chain:

```
F (h, φ h) < ((m+1 : ℕ) : ℝ≥0∞) * ε'
           = (m : ℝ≥0∞) * ε' + ε'        -- push_cast, add_mul, one_mul
           ≤ g h + ε'                      -- add_le_add_right (band lower bound)
```

**Step 7 (conclude).** In both cases `F (h, φ h) ≤ g h + ε' ≤ g h + ε`
(`add_le_add_left hε'ε`). ∎

*Remark (strict version, free).* On `{g < ∞}` the case-`m+1` chain is
strict: `F (h, φ h) < g h + ε' ≤ g h + ε`. If ever wanted, add the extra
conclusion `∀ h, g h < ∞ → F (h, φ h) < g h + ε` — zero new ideas. Not
needed by the application; omit from the first formalization pass.

*Size estimate §2:* ~180–240 lines total (P4.1: 5, P4.2: 10, P4.3: 20,
P4.4: 10 (+15 fallback), P4.5: 25, P4.6: 90–120 incl. doc comments).

---

## §3. Application half — ε-optimal measurable strategies for bicausal OT

Suggested location: new file `BicausalOT/MeasurableStrategy.lean`
(imports `MultiPeriod`, `EpsOptimalSelection`, `ProbabilityMeasurePolish`,
and the Phase-3 file). Standing variables (the Phase-3 context):

```lean
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  -- same four for Y n
  -- Phase-3 D1 instances give: TopologicalSpace/PolishSpace/BorelSpace
  -- on PairHist X Y t and XHist/YHist, compatible with the product
  -- MeasurableSpace structure used by Feas.
variable {κμ : (t : ℕ) → XHist X t → Measure (X (t + 1))}
  {κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1))}
  {c : (t : ℕ) → PairHist X Y t → ℝ≥0∞}
```

### P4.7 (Phase-3 interface — consumed, not proved here)

Exactly three statements are needed from Phase 3; pin them now so E1 and
E2 stay compatible. (If Phase 3 lands with different names, only this
block changes.)

```lean
-- (a) Phase-3 main theorem (BS 8.2 analogue)
theorem VGo_lowerSemianalytic
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hκμ_meas : ∀ t, Measurable (κμ t)) (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y)) :
    ∀ k t, IsLowerSemianalytic (VGo c κμ κν k t)

-- (b) the feasibility graph, reindexed over probability measures
def GammaSet (κμ) (κν) (t : ℕ) :
    Set (PairHist X Y t × ProbabilityMeasure (X (t+1) × Y (t+1))) :=
  {p | (p.2 : Measure (X (t+1) × Y (t+1))) ∈ Feas κμ κν t p.1}

theorem measurableSet_gammaSet … : MeasurableSet (GammaSet κμ κν t)
-- (Phase-3 D3 equalizer route: h ↦ (κμ t (projX t h), κν t (projY t h))
--  Borel; γ ↦ (γ.map fst, γ.map snd) continuous on P(W); diagonal closed.)
-- Phase 4 only uses the corollary:
theorem analyticSet_gammaSet … : AnalyticSet (GammaSet κμ κν t)
  -- := (measurableSet_gammaSet …).analyticSet   (ambient Polish: D1 × W1)

-- (c) BS 7.48 applied to the evaluation kernel (h, γ) ↦ ↑γ
theorem stageF_lowerSemianalytic … (k t : ℕ) :
    IsLowerSemianalytic (X := PairHist X Y t × ProbabilityMeasure _)
      (fun p => ∫⁻ z, VGo c κμ κν k (t + 1) (p.1, z)
        ∂(p.2 : Measure (X (t+1) × Y (t+1))))
-- (via lintegral_lowerSemianalytic: κ := fun p => ↑p.2 is Measurable
--  (W2 ∘ measurable_snd; borel(product) = product of borels — second
--  countable) and Markov; integrand lsa by
--  AnalyticSet.preimage_of_continuous along ((h,γ),z) ↦ (h,z).)
```

### P4.8 (fiber nonemptiness of `GammaSet`)

```lean
theorem gammaSet_fiber_nonempty
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    (t : ℕ) (h : PairHist X Y t) :
    ∃ γp : ProbabilityMeasure (X (t+1) × Y (t+1)), (h, γp) ∈ GammaSet κμ κν t
```

*Proof.* `hne t h` gives `γm ∈ Feas`; `Feas.measure_univ κμ κν hκμ` (L0)
gives `γm univ = 1`; `IsProbabilityMeasure ⟨·⟩` constructor;
`γp := ⟨γm, this⟩`; membership is `rfl`-level (subtype coercion). ~8 lines.

### P4.9 (infimum reindexing: `Feas`-inf = `GammaSet`-fiber-inf)

```lean
theorem iInf_feas_eq_iInf_gammaSet
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (t : ℕ) (h : PairHist X Y t) (f : X (t+1) × Y (t+1) → ℝ≥0∞) :
    (⨅ (γm : Measure (X (t+1) × Y (t+1))) (_ : γm ∈ Feas κμ κν t h),
      ∫⁻ z, f z ∂γm)
    = ⨅ (γp : ProbabilityMeasure (X (t+1) × Y (t+1)))
        (_ : (h, γp) ∈ GammaSet κμ κν t),
      ∫⁻ z, f z ∂(γp : Measure _)
```

*Proof.* `le_antisymm`. (≤): `le_iInf₂ fun γp hγp => iInf₂_le _ hγp`
(the coerced measure IS in `Feas` by definition of `GammaSet`).
(≥): `le_iInf₂ fun γm hγm =>`; upgrade `γm` to
`γp := ⟨γm, IsProbabilityMeasure …⟩` via L0 as in P4.8; then
`iInf₂_le γp hγm` — the integrals agree definitionally (`↑γp = γm` is
`rfl`). ~15 lines. NOTE: this lemma (or its `iInf`-shape twin) is very
likely already part of the Phase-3 E1 draft (its induction step needs the
same reindexing); if so, REUSE — do not duplicate. Stated with a general
`f` so one lemma serves every depth.

### P4.10 (σ(Σ¹₁) → Giry transport of the selector)

```lean
-- (a) Polish wrapper of W2 (mirror the instPolishSpace upgrade pattern,
--     ProbabilityMeasurePolish.lean:624–630)
theorem probabilityMeasure_borel_measurable_toMeasure_polish
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] :
    @Measurable (ProbabilityMeasure Ω) (Measure Ω)
      (borel (ProbabilityMeasure Ω)) inferInstance (↑) := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable Ω
  exact probabilityMeasure_borel_measurable_toMeasure
-- SOUND because the upgrade only re-metrizes: the topology of Ω, hence
-- the weak topology on P(Ω), hence borel (P(Ω)) and the Giry σ-algebra,
-- are unchanged. Mirror the exact green pattern of
-- ProbabilityMeasure.instPolishSpace (ProbabilityMeasurePolish.lean:626-632).

-- (b) composition: analytically measurable P(Ω)-valued maps are
--     σ(Σ¹₁)-to-Giry measurable as Measure-valued maps
theorem AnalyticallyMeasurable.toMeasure_comp
    {H Ω : Type*} [TopologicalSpace H] [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    {φ : H → ProbabilityMeasure Ω} (hφ : AnalyticallyMeasurable φ) :
    @Measurable H (Measure Ω) (analyticMeasurableSpace H) inferInstance
      (fun h => (φ h : Measure Ω)) :=
  probabilityMeasure_borel_measurable_toMeasure_polish.comp hφ
```

`AnalyticallyMeasurable φ` unfolds to
`@Measurable H (P Ω) (analyticMeasurableSpace H) (borel _) φ`, so the
composition is a plain `Measurable.comp` with matched middle instance
`borel (ProbabilityMeasure Ω)`. ~12 lines total.

### P4.11 (MAIN — measurable ε-optimal strategy; upgrades L3)

```lean
/-- **Phase-4 main theorem** (BS 7.50 for the bicausal Bellman recursion):
an analytically-measurable, pointwise-feasible, stage-wise ε-optimal
strategy for horizon `T` — the measurable upgrade of
`MultiPeriod.exists_eps_strategy`. -/
theorem exists_eps_strategy_analyticallyMeasurable (T : ℕ)
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hκμ_meas : ∀ t, Measurable (κμ t)) (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γε : Strat X Y,
      (∀ t h, γε t h ∈ Feas κμ κν t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
          ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) ∧
      (∀ t, ∃ φ : PairHist X Y t → ProbabilityMeasure (X (t+1) × Y (t+1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γε t h = (φ h : Measure _))
```

*Proof.* For each `t : ℕ` invoke P4.6 with

- `H := PairHist X Y t` (Polish: Phase-3 D1), `E := ProbabilityMeasure (W t)`
  (Polish: W1 `ProbabilityMeasure.instPolishSpace`);
- `Γ := GammaSet κμ κν t`, analytic by P4.7(b);
- `F := fun p => ∫⁻ z, VGo c κμ κν (T - t - 1) (t+1) (p.1, z) ∂↑p.2`,
  lsa by P4.7(c) at depth `k := T - t - 1` (which needs P4.7(a));
- `hfib := gammaSet_fiber_nonempty hκμ hne t` (P4.8); `hε`.

This yields (for each `t`) `φ t` with `AnalyticallyMeasurable (φ t)`,
`∀ h, (h, φ t h) ∈ GammaSet κμ κν t`, and
`∀ h, F (h, φ t h) ≤ (⨅ γp ∈ fiber, F (h, γp)) + ε`.
Package with `choose φ hmeas hmem hopt using key` across `t` and set
`γε := fun t h => (φ t h : Measure _)`. Then:

1. Feasibility: `hmem t h` IS `γε t h ∈ Feas κμ κν t h` (unfold `GammaSet`).
2. ε-optimality: `hopt t h` rewritten with
   `(iInf_feas_eq_iInf_gammaSet hκμ t h _).symm` (P4.9, at
   `f := fun z => VGo c κμ κν (T-t-1) (t+1) (h, z)`); the LHS integral is
   definitionally `∫⁻ z, … ∂(γε t h)`.
3. Measurability clause: `⟨φ t, hmeas t, fun h => rfl⟩`.

Exactly like L3, the statement quantifies over ALL `t` with the
`Nat`-truncated depth `T - t - 1` and needs no `t < T` guard — each stage's
selection problem is posed at its own fixed depth, so there is no
cross-depth conflict (Phase-2 battle-log simplification carries over
verbatim). ~60–80 lines.

*Corollary (Giry measurability, one line per stage):*

```lean
theorem eps_strategy_measurable_toMeasure … :
    ∀ t, @Measurable (PairHist X Y t) (Measure (X (t+1) × Y (t+1)))
      (analyticMeasurableSpace (PairHist X Y t)) inferInstance (γε t)
  -- := fun t => (hφ t).toMeasure_comp  (P4.10b)
```

### P4.12 (corollary — the measurable strategy is Tε-optimal for the value)

`γε` from P4.11 satisfies EXACTLY the `hopt` hypothesis shape of L4
(`costGo_le_VGo_add`), with the same `hmem`. Hence, with no new proof:

```lean
theorem costGo_le_VGo_add_measurable … (γε …from P4.11…) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γε k t h ≤ VGo c κμ κν k t h + (k : ℝ≥0∞) * ε
  -- := costGo_le_VGo_add κμ κν c T hκμ γε hmem hopt
```

and at `(k, t) = (T, 0)`:
`costGo c γε T 0 h₀ ≤ VGo c κμ κν T 0 h₀ + T·ε` pointwise; integrating
against any `γ₀ ∈ CouplingSet₀ μ₀ ν₀` (mass 1) reproduces the L5 upper
bound **with a measurable strategy** — i.e. the infimum in
`bellman_value_eq_multi` may be restricted to stage-wise
σ(Σ¹₁)-measurable strategies without changing its value. Optional named
corollary `bellman_value_eq_multi_measurable` (restate L5's LHS with the
extra measurability constraint on the strategy inf; ≥ is inherited, ≤ via
γε above): worth stating, ~30 lines, decide at attack time.

*Size estimate §3:* ~200–260 lines (excluding the Phase-3 interface items).

---

## §4. ADVERSARIAL VERIFICATION of the band gluing

(No Agent tool was available in this session; this pass was executed
in-line, systematically, against the checklist requested by the front
prompt. Each item was checked against the exact repo signatures.)

1. **`g h = ∞` fibers.** `p 0 h` holds, `Nat.find = 0` (least index), so
   `φ h = φ∞ h`: feasible via P4.2 (needs only fiber-nonemptiness at `h`,
   which `hfib` gives), and `F ≤ ⊤ = g h ≤ g h + ε` — sound even when
   `F (h, φ∞ h) = ∞`. No band lemma is ever invoked with an infinite `g h`:
   `p (m+1) h` would require `g h < (m+1)·ε' ≤ (m+1) < ∞`, impossible. ✓
2. **Conversely, finite `g h` never lands in the fallback:** `p 0 h` is
   `g h = ∞`, false; `Nat.find ≥ 1`; existence of SOME satisfied index is
   P4.5 `exists_band` (Archimedean step needs `ε' ≠ 0`, `ε' ≠ ∞`, `g h ≠ ∞`
   — all in context). ✓
3. **Band boundaries.** Bands realized by `Nat.find` are exactly
   `[m·ε', (m+1)·ε')` — left-closed, right-open, pairwise disjoint,
   covering `[0, ∞)`. Boundary case `g h = m·ε'` (`m ≥ 1`): `p m h` fails
   (`¬(g h < m·ε')`), `p (m+1) h` holds (`g h = m·ε' < m·ε' + ε' = (m+1)·ε'`,
   finiteness ✓), so `Nat.find = m+1` (if not smaller — smaller is
   impossible since `p j`, `j ≤ m`, all fail); the bound chain is tight but
   valid: `F < (m+1)·ε' = g h + ε'`. ✓
4. **Empty `Feas` fibers.** Excluded by `hne` (hypothesis, load-bearing:
   without it `h ∉ Prod.fst '' Γ` and JvN guarantees nothing at `h`; both
   feasibility and the `g h = ∞ ⇒ trivial` argument would break — note
   `g h = ⨅ over ∅ = ∞` on empty fibers, which would route such `h` to the
   fallback band where P4.2's conclusion is exactly what fails). The
   abstract theorem therefore carries `hfib` explicitly. Synergy: WAVE-3
   front F1 aims to PROVE `hne` from product couplings — when it lands,
   P4.11's `hne` hypothesis can be discharged, not just assumed. ✓
5. **Empty `H` (e.g. some `X s` empty makes `PairHist t` empty).** Handled
   in Step 0 by `isEmptyElim`; measurability trivial. The final assembly
   never needs `Nonempty (PairHist t)`. ✓
6. **Empty selection sets `A q`.** If `A ((m+1)·ε') = ∅` then no `h` has
   `Nat.find = m+1` (that would produce a fiber witness via P4.1), so the
   `χ (m+1) := φ∞` fallback branch of P4.3 is only ever evaluated at
   irrelevant `h` — its ∀-clause is vacuously true, which is all P4.6 uses.
   The dite condition `(A q).Nonempty` is a global Prop about the SET (not
   about `h`), so no measurability leakage; `dif_pos` with the in-proof
   nonemptiness witness is fine by proof irrelevance. ✓
7. **Overlapping band predicates.** `{p m}` are NOT disjoint (`p (m+1)`
   is monotone-ish in `m`); correctness only ever uses (i) `Nat.find`'s
   spec at the least index and (ii) minimality below it. The glue lemma
   P4.4 requires coverage only — disjointness of effective pieces
   `{Nat.find = m}` is automatic. ✓
8. **`ε` edge cases.** `ε = ∞` or `ε > 1`: `ε' = min ε 1` keeps every
   band product `(m+1)·ε'` finite (so the strict inequalities behave) and
   the final weakening `g + ε' ≤ g + ε` is monotonicity of `+` in `ℝ≥0∞`.
   `ε ≤ 1`: `ε' = ε`, nothing changes. `0 < ε'` always (`lt_min hε
   zero_lt_one`). No subtraction, no division except the Archimedean step
   `g h / ε'` guarded by `ε' ≠ 0, ≠ ∞, g h ≠ ∞`. ✓
9. **The two σ(Σ¹₁) generators are genuinely needed.** `{p 0}` uses a
   CO-analytic set (complement of `{g < ⊤}`); `{p (m+1)}` uses analytic
   sets; the selection sets `A q` use only `F`-sublevels (analytic) — the
   partition of labor claimed in §1.2 is honored exactly; at no point is
   an analytic-ness claim made about a superlevel of `g` or any set
   involving `g` from above. ✓
10. **Instance hygiene (the sneaky one).** `ProbabilityMeasure Ω` is a
    subtype of `Measure Ω`, so Mathlib's `Subtype.instMeasurableSpace`
    (comap of the Giry σ-algebra) exists and could silently capture a bare
    `Measurable` into `P(W)`. Phase 4 never writes such a statement: the
    abstract theorem puts NO `MeasurableSpace` on `E` (it uses
    `AnalyticallyMeasurable`, which pins `borel E` in its definition), and
    the application composes explicitly via P4.10 with `@`-pinned
    instances. W2 guarantees Giry ≤ borel(weak) so the composition
    direction is the safe one. If Phase 3's `WeakP` type synonym lands,
    the application can switch to it transparently. ✓
11. **Depth consistency.** Stage `t` selects against the FIXED integrand
    `VGo (T-t-1) (t+1)`; `costGo _ T 0` only ever evaluates `γε t` at that
    depth (Phase-2 design (a)); the P4.12 corollary type-checks against L4
    verbatim because P4.11's clause 2 is syntactically L3's clause (ii). ✓
12. **JvN preconditions at every call site.** Call 1 (P4.2): `Γ` analytic
    (hyp), `Γ.Nonempty` (Step 0). Call 2 (P4.3): `A q` analytic
    (`inter'`, ambient T2 from Polish), `A q` nonempty (dite guard). The
    uniformization property is only ever used at `h ∈ Prod.fst '' ·`,
    established by explicit image witnesses both times. ✓
13. **`iInf_fiber` preconditions.** `Γ` analytic ✓, `F` lsa ✓, `[T2Space H]`
    from Polish/metrizable instance chain (flag: may need a `haveI`;
    Phase-3 uses the same lemma so any friction is already solved there). ✓

Conclusion of the adversarial pass: **no gap found**; two required
hypotheses (`hne`, Phase-3 interface) and one Lean-side hazard (item 10)
are explicitly tracked.

### §4.1 Second independent adversarial pass (2026-07-10, relaunched E2)

A fresh session re-executed the verification from scratch against the
repository (no Agent tool exposed; pass run in-line but independent of the
2026-07-07 pass). Every interface citation was re-checked against source:

- `jankov_von_neumann` Tree.lean:284 — both preconditions (`AnalyticSet P`,
  `P.Nonempty`) and the image-restricted uniformization clause match §0. ✓
- `IsLowerSemianalytic` (∀ c : ℝ≥0∞ incl. ⊤) and `iInf_fiber`
  (LowerSemianalytic.lean:18/35, explicit `[T2Space X]`) match. ✓
- `inter'` KernelIntegral.lean:32 (`[T2Space W]`),
  `preimage_of_continuous` :53, `lintegral_lowerSemianalytic` :283
  (hypotheses `Measurable κ`, `∀ x, IsProbabilityMeasure (κ x)`) match. ✓
- MultiPeriod.lean: `Feas` :56, L0 :86, L3 :122 (no `t < T` guard — P4.11's
  clause 2 is syntactically L3's clause (ii) ✓), L4 :145 (`hopt` shape
  consumed verbatim by P4.12 ✓).
- `AnalyticallyMeasurable` = `@Measurable _ _ (analyticMeasurableSpace X)
  (borel Y)` (AnalyticSigmaAlgebra.lean:48), `mem`/`compl_mem` :23/:28. ✓
- Mathlib `Measurable.find` Constructions.lean:507 — domain σ-algebra is an
  anonymous `{_ : MeasurableSpace α}`, so the P4.4 route-1 instantiation at
  `analyticMeasurableSpace H` is legitimate; `[∀ n, DecidablePred (p n)]`
  and codomain `[MeasurableSpace β]` (pin `borel E`) as stated. ✓

Independent re-derivations (all reproduced the design's conclusions):

- **`Nat.find` index audit.** For finite `g h`, `Nat.find = m+1` gives via
  `Nat.find_min` exactly `¬ p j` for `j ≤ m`; `band_lower_bound`'s case
  split (`m = 0` trivial; `m = j+1` from `¬ p (j+1)` via `not_lt`) is
  index-correct; no off-by-one. ✓
- **Boundary `g h = m·ε'` (`m ≥ 1`).** `p j` fails for all `j ≤ m`
  (`m·ε' < j·ε' ↔ m < j` for `ε' ≠ 0, ≠ ∞`), `p (m+1)` holds
  (`m·ε' < (m+1)·ε'` needs `0 < ε'` and finiteness — both in context);
  chain `F < (m+1)·ε' = g h + ε'` tight but valid. ✓
- **`exists_band` arithmetic.** `ENNReal.div_lt_iff` orientation
  (`v/ε' < n ↔ v < n·ε'`), guard `v/ε' ≠ ∞` from `ε' ≠ 0 ∧ v ≠ ∞`
  (`ENNReal.div_eq_top`), `n ≠ 0` since `v < 0·ε' = 0` is absurd. ✓
- **`q = 0` degeneration.** `A 0 = ∅` (nothing `< 0` in `ℝ≥0∞`), absorbed
  by P4.3's vacuous fallback branch. ✓
- **Cross-band contamination impossible.** Finite `g h` never routes to the
  fallback (`p 0` false), infinite `g h` never enters a finite band
  (`(m+1)·ε' ≤ (m+1) < ∞`). ✓
- **New finding (fixed).** The application ambient needs
  `BorelSpace (X (t+1) × Y (t+1))` for W1's `instPolishSpace`; confirmed
  available as Mathlib `Prod.borelSpace` (BorelSpace/Basic.lean:642) under
  `SecondCountableTopologyEither`, given by Polish — recorded as R11.
- **Stale citations (fixed).** W2 line 716→718, `instPolishSpace` 624→626.

Verdict of the second pass: **the mathematical argument stands unchanged**;
only citation hygiene and one instance pin were amended.

---

## §5. Constants summary (single source of truth)

| Quantity | Value | Where used |
|---|---|---|
| Normalized tolerance | `ε' := min ε 1` | Steps 1–7 of P4.6 |
| Band grid | `m · ε'`, `m : ℕ` | P4.5 |
| Band `m` (effective) | `{h | m·ε' ≤ g h < (m+1)·ε'}` | Step 6 |
| Selection threshold on band `m` | `q = (m+1)·ε'` (band's upper edge) | P4.3 call |
| Achieved slack | `< ε'` on `{g < ∞}`, `≤ 0` trivial on `{g = ∞}` | Step 6/7 |
| Band width needed | `ε'` (NOT `ε/2` — threshold at top edge vs `g ≥` bottom edge) | §1.2 |

## §6. Risk list

| # | Risk | Phase-4 impact | Mitigation |
|---|---|---|---|
| R1 | Phase-3 interface drift (P4.7 a–c shapes/names) | blocks §3 only | §2 is fully independent — formalize `EpsOptimalSelection.lean` NOW; §3 written against the pinned P4.7 block; worst case, take P4.7 items as hypotheses of P4.11 to decouple compile order |
| R2 | `Subtype` σ-algebra on `ProbabilityMeasure` captured by a bare `Measurable` | silent wrong statement | never state bare `Measurable` into `P(W)`; use `AnalyticallyMeasurable` + `@Measurable` with pinned instances (adversarial item 10); adopt Phase-3 `WeakP` synonym if it lands |
| R3 | `Measurable.find` signature/`DecidablePred` friction | P4.4 | `open scoped Classical`; fallback manual proof included in P4.4 (route 2, ~15 lines) |
| R4 | `T2Space H` instance for `iInf_fiber` not found by TC | P4.6 Step 2 | `haveI`/`letI` from Polish→metrizable→T2; identical friction already faced by Phase 3 |
| R5 | `upgradeIsCompletelyMetrizable` in P4.10a shifting instances | wrong borel | mirror the exact green pattern of `ProbabilityMeasure.instPolishSpace` (ProbabilityMeasurePolish.lean:626–632); topology unchanged ⇒ borel unchanged |
| R6 | `ENNReal.div_lt_iff` / `exists_nat_gt` exact signatures | P4.5 | both confirmed to exist; disjunctive hypotheses of `div_lt_iff` satisfied by `ε' ≠ 0, ≠ ∞`; 5-line inline fallback: induction-free `le_of_not_lt` + `ENNReal.lt_iff_exists_nat_btwn`-style alternatives |
| R7 | `borel (H × P(W)) =` product σ-algebra (needed inside P4.7c) | Phase-3 risk, not ours | second-countability of both factors (Polish); tracked in Phase-3 plan |
| R8 | `Nat.find` spec extraction at successor index (off-by-one) | P4.6 Step 6 | band predicate deliberately defined by pattern `p 0 / p (m+1)` — no `Nat` subtraction anywhere; minimality consumed via P4.5 `band_lower_bound` with `m` cases |
| R9 | Axiom audit | none expected | entire chain factors through JvN + `choose` + dite: `[propext, Classical.choice, Quot.sound]` only, same as the 30 audited theorems |
| R10 | Universe polymorphism (`PairHist : Type (max u v)`) | none expected | P4.6 is `{H E : Type*}`-polymorphic like `jankov_von_neumann` |
| R11 | `BorelSpace (X (t+1) × Y (t+1))` needed by `instPolishSpace` at the P4.11 call sites (`E := ProbabilityMeasure (W t)`) | instance search failure | CONFIRMED available: Mathlib `instance Prod.borelSpace` (`MeasureTheory/Constructions/BorelSpace/Basic.lean:642`), hypothesis `[SecondCountableTopologyEither α β]` discharged by Polish ⇒ second countable; negligible |

## §7. Attack order and wiring

1. `EpsOptimalSelection.lean` (P4.1–P4.6) — attack NOW, independent of
   Phase 3; compile via `lake env lean`.
2. P4.10 (a)+(b) — independent of Phase 3 as well (only W1/W2); can live at
   the end of `EpsOptimalSelection.lean` or in `ProbabilityMeasurePolish.lean`.
3. After Phase-3 E1 integration: `MeasurableStrategy.lean`
   (P4.8, P4.9 [reuse E1's if present], P4.11, P4.12).
4. Wire `exists_eps_optimal_selector`,
   `exists_eps_strategy_analyticallyMeasurable`, and the P4.12 corollary
   into `Basic.lean` + `AxiomsAudit.lean`.

Total estimate: ~380–500 new lines, expected 4–7 compile-fix rounds
(dominated by instance pinning and `ℝ≥0∞` cast normalization).
