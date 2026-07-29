# F1 — Nonemptiness of feasible sets: which hypotheses die, and how

Companion to `draft_FeasNonempty.lean` (compiled 2026-07-10 against the green
repo: `lake env lean` exit 0, 0 errors / 0 warnings; all 8 new theorems
`#print axioms`-clean: `[propext, Classical.choice, Quot.sound]`).

## 1. The witness

The (conditionally) independent product coupling. Mathlib already has the
marginal computation: `Measure.map_fst_prod : (μ.prod ν).map Prod.fst =
(ν univ) • μ` (needs `[SFinite ν]`, in scope) and symmetrically
`Measure.map_snd_prod`. For probability factors the scalar is `1 •` and
vanishes; the draft wraps this once and for all as

- `MeasureTheory.Measure.map_fst_prod_of_isProbabilityMeasure (μ) (ν)
  [IsProbabilityMeasure ν] : (μ.prod ν).map Prod.fst = μ`
- `MeasureTheory.Measure.map_snd_prod_of_isProbabilityMeasure (μ) (ν)
  [IsProbabilityMeasure μ] [SFinite ν] : (μ.prod ν).map Prod.snd = ν`

(One-line alternative proofs: `measurePreserving_fst.map_eq` /
`measurePreserving_snd.map_eq`, same file `Mathlib/MeasureTheory/Measure/
Prod.lean`. Both wrappers are Mathlib-PR candidates.)

## 2. Exactly which hypotheses become redundant

### T = 1, `bellman_value_eq` (ValueRepresentation.lean)

Current hypotheses:

| hypothesis | status |
|---|---|
| `h_Gamma_ne : ∀ z₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty` | redundant **given the new probability-kernel hypotheses** `hκμ : ∀ x, IsProbabilityMeasure (κ_μ x)`, `hκν : ∀ y, IsProbabilityMeasure (κ_ν y)` — discharge by `FeasibleSet₀.nonempty` |
| `h_prob : ∀ γ₀ ∈ CouplingSet₀ μ₀ ν₀, γ₀ Set.univ ≤ 1` | redundant **outright**: already derivable from the existing `[IsProbabilityMeasure μ₀]` instance via `CouplingSet₀.measure_univ` (Blueprint §2.3 L5 predicted this: "proving it is 3 lines with map_apply"). No new hypothesis needed. |

The same applies to `bellman_value_leq` (both hypotheses) and
`bellman_value_leq_aux` / `eps_optimal_kernel_bound` (`h_Gamma_ne` only).
Recommendation: leave the aux lemmas untouched (they are correctly general),
add only the top-level primed corollary.

### Multi-period, `MultiPeriod.bellman_value_eq_multi` (MultiPeriod.lean)

Current hypotheses: `hκμ : ∀ t x, IsProbabilityMeasure (κμ t x)` and
`hne : ∀ t h, (Feas κμ κν t h).Nonempty`.

`hne` becomes redundant given the **new, symmetric** hypothesis
`hκν : ∀ t y, IsProbabilityMeasure (κν t y)` — discharge by
`MultiPeriod.Feas.nonempty` (witness `(κμ t (projX t h)).prod (κν t (projY t h))`).

Trade-off note: the unprimed theorem never needs anything about `κν`
(only the X-side mass enters L0/L4), so the primed version is not strictly
more general — it trades a quantified-over-all-histories nonemptiness
condition (unverifiable in practice) for the standard Markov-kernel
condition on `κν`. In every intended application both families are
probability kernels, so the primed form is the user-facing one.

`MultiPeriod.exists_eps_strategy` also carries `hne`; callers can now feed
it `Feas.nonempty κμ κν hκμ hκν`. No primed variant recommended (internal
lemma).

## 3. Recommended new statements (all compiled in the draft)

Keep `bellman_value_eq` and `bellman_value_eq_multi` unchanged for
compatibility; add:

```lean
theorem bellman_value_eq'                      -- ValueRepresentation.lean
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀) [IsProbabilityMeasure ν₀]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y)) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    = ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ :=
  bellman_value_eq c₀ c₁ μ₀ ν₀ κ_μ κ_ν
    (FeasibleSet₀.nonempty κ_μ κ_ν hκμ hκν)
    (fun _ hγ₀ => le_of_eq (CouplingSet₀.measure_univ hγ₀))
```

```lean
theorem MultiPeriod.bellman_value_eq_multi' (T : ℕ)   -- MultiPeriod.lean
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y)) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ :=
  bellman_value_eq_multi κμ κν c T μ₀ ν₀ hκμ (Feas.nonempty κμ κν hκμ hκν)
```

Supporting lemmas (also in the draft): `prod` marginal wrappers (§1),
`CouplingSet₀.nonempty`, `CouplingSet₀.measure_univ`,
`FeasibleSet₀.nonempty`, `MultiPeriod.Feas.nonempty`.

## 4. Integration plan for the main loop

1. Marginal wrappers + `CouplingSet₀.nonempty` + `CouplingSet₀.measure_univ`
   + `FeasibleSet₀.nonempty` → `Defs.lean` (they need nothing beyond its
   imports; note `FeasibleSet₀.nonempty` carries
   `omit [MeasurableSpace X₀] [MeasurableSpace Y₀] in`, placed BEFORE the
   doc comment — after it is a parse error).
2. `bellman_value_eq'` → end of `ValueRepresentation.lean`.
3. `Feas.nonempty` + `bellman_value_eq_multi'` → end of `MultiPeriod.lean`.
4. `AxiomsAudit.lean`: add (at least) `FeasibleSet₀.nonempty`,
   `CouplingSet₀.measure_univ`, `bellman_value_eq'`,
   `MultiPeriod.Feas.nonempty`, `MultiPeriod.bellman_value_eq_multi'`.
5. Optional cleanup: the inline `hγ₀mass` block inside
   `bellman_value_eq_multi` (MultiPeriod.lean, ~lines 204–208) duplicates
   `CouplingSet₀.measure_univ`; replace once the lemma lands in Defs.lean.
6. F2/F3 synergy (other fronts): `Feas.nonempty` + closedness/compactness
   of the coupling sets upgrades conditional existence to unconditional
   existence of optimizers — the primed corollaries here are the
   hypothesis-free interface those fronts should target.
