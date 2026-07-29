/-
  Phase 5: exact Borel-measurable optimal strategies — the Feller/lsc model
  (Bertsekas–Shreve Chapter 8.3, lower semicontinuous model analogue)

  Blueprint: BLUEPRINT.md §4F. Under kernels weakly continuous in the
  history (Feller, taken as `ProbabilityMeasure`-valued primitives) and
  lower semicontinuous stage costs:
  · the Bellman value functions are genuinely lower semicontinuous
    (`lowerSemicontinuous_VGo` — Berge backward induction over the
    sequentially upper hemicontinuous, compact-valued feasibility
    correspondence, with the jointly lsc integral pairing of
    LscIntegral.lean);
  · the exact argmin correspondence is nonempty, closed-valued and
    weakly measurable (`argminSet_*` — the constrained-value comparison
    `stageMin C ≤ stageMin univ` over an Fσ decomposition of opens);
  · Kuratowski–Ryll-Nardzewski selection yields a strategy that is
    EXACTLY optimal at every stage and plain-Borel measurable
    (`exists_optimal_measurable_strategy`), and the Bellman value is
    ATTAINED: `costGo = VGo` (`bellman_value_attained_measurable`) —
    the ε = 0, plain-Borel upgrade of Phases 2 and 4 under stronger
    hypotheses (twin track: neither result dominates the other).
-/
import BicausalOT.MeasurableStrategy
import BicausalOT.DescriptiveSetTheory.CouplingsUHC
import BicausalOT.DescriptiveSetTheory.LscIntegral
import BicausalOT.DescriptiveSetTheory.MeasurableSelection

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

/-! ## KRN on the Polish space of probability measures -/

/-- Kuratowski–Ryll-Nardzewski selection with `WeakP` targets: the Polish
    wrapper of `exists_measurable_selection` (the metric upgrade keeps the
    topology, hence the Borel structure — the §3W C3 pattern). -/
theorem WeakP.exists_measurable_selection {α : Type*} [MeasurableSpace α]
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W]
    [BorelSpace W]
    {Φ : α → Set (WeakP W)} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set (WeakP W), IsOpen U →
      MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → WeakP W, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (WeakP W)
  exact _root_.exists_measurable_selection hne hclosed hmeas

namespace MultiPeriod

variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]

variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

/-! ## The feasibility fibers: compact and nonempty -/

/-- Fibers of the feasibility graph at probability kernels are compact in
    the weak topology (couplings of fixed marginals are compact). -/
theorem isCompact_feasGraph_fiber (t : ℕ) (h : PairHist X Y t) :
    IsCompact {γ : WeakP (X (t + 1) × Y (t + 1)) |
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} :=
  isCompact_probabilityMeasure_marginals
    (κμP t (projX t h) : Measure (X (t + 1)))
    (κνP t (projY t h) : Measure (Y (t + 1)))

omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)] in
/-- Fibers of the feasibility graph at probability kernels are nonempty
    (product coupling, F1). -/
theorem feasGraph_fiber_nonempty' (t : ℕ) (h : PairHist X Y t) :
    ∃ γ : WeakP (X (t + 1) × Y (t + 1)),
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t :=
  feasGraph_fiber_nonempty _ _ (fun _ _ => inferInstance)
    (Feas.nonempty _ _ (fun _ _ => inferInstance) (fun _ _ => inferInstance))
    t h

/-! ## The constrained one-step value -/

/-- Constrained one-step value: the infimum of a stage objective over the
    feasible fiber intersected with a constraint set. `C = univ` recovers
    the one-step Bellman infimum. -/
def stageMin (t : ℕ)
    (F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞)
    (C : Set (WeakP (X (t + 1) × Y (t + 1)))) (h : PairHist X Y t) : ℝ≥0∞ :=
  ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
    (_ : (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
      (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧ γ ∈ C), F (h, γ)

omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)] in
/-- The one-step Bellman recursion through the unconstrained
    `stageMin`. -/
theorem VGo_succ_eq_stageMin (k t : ℕ) (h : PairHist X Y t) :
    VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) (k + 1) t h
      = c t h + stageMin κμP κνP t
          (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
            ∂p.2.toMeasure) univ h := by
  rw [VGo_succ_eq_weakP _ _ c (fun _ _ => inferInstance) k t h]
  congr 1
  simp only [stageMin, Set.mem_univ, and_true]

/-! ## Berge minimum: the constrained value is lower semicontinuous -/

/-- **Berge minimum (parametrized).** In the Feller model, the constrained
    one-step value against a jointly lower semicontinuous objective and a
    closed constraint set is lower semicontinuous in the history:
    minimizers along a convergent sequence of histories have convergent
    marginals, hence are tight; Prokhorov extracts a convergent
    subsequence whose limit is feasible, constrained, and no worse. -/
theorem lowerSemicontinuous_stageMin
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    LowerSemicontinuous (stageMin κμP κνP t F C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hy
  · rw [Set.Iic_top, Set.preimage_univ]
    exact isClosed_univ
  refine IsSeqClosed.isClosed fun hs h hmem hlim => ?_
  simp only [Set.mem_preimage, Set.mem_Iic] at hmem ⊢
  -- select minimizers along the sequence
  have hsel : ∀ n, ∃ γ : WeakP (X (t + 1) × Y (t + 1)),
      ((hs n, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧ γ ∈ C) ∧
      F (hs n, γ) ≤ y := by
    intro n
    have hfibne : ∃ γ, (hs n, γ) ∈ FeasGraph
        (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧ γ ∈ C := by
      by_contra hempty
      have htop : stageMin κμP κνP t F C (hs n) = ⊤ :=
        iInf_eq_top.mpr fun γ => iInf_eq_top.mpr fun hcond =>
          absurd hcond (not_exists.mp hempty γ)
      have := hmem n
      rw [htop] at this
      exact hy (top_le_iff.mp this)
    obtain ⟨γ₀, hγ₀⟩ := hfibne
    have hcomp : IsCompact ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (hs n, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C) :=
      (isCompact_feasGraph_fiber κμP κνP t (hs n)).inter_right hC
    have hne' : ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (hs n, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty :=
      ⟨γ₀, hγ₀.1, hγ₀.2⟩
    obtain ⟨γn, hγn_mem, hγn_min⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne' hcomp
        ((hF.comp (Continuous.prodMk continuous_const continuous_id)
          ).lowerSemicontinuousOn _)
    refine ⟨γn, ⟨hγn_mem.1, hγn_mem.2⟩, ?_⟩
    refine le_trans (le_trans ?_ (le_refl (stageMin κμP κνP t F C (hs n))))
      (hmem n)
    exact le_iInf₂ fun γ' hγ' => isMinOn_iff.mp hγn_min γ' ⟨hγ'.1, hγ'.2⟩
  choose γs hγs_cond hγs_le using hsel
  -- marginal convergence via Feller continuity of the kernels
  have hμ : Tendsto (fun n => κμP t (projX t (hs n))) atTop
      (𝓝 (κμP t (projX t h))) :=
    (((hκμ_cont t).comp (continuous_projX t)).tendsto h).comp hlim
  have hν : Tendsto (fun n => κνP t (projY t (hs n))) atTop
      (𝓝 (κνP t (projY t h))) :=
    (((hκν_cont t).comp (continuous_projY t)).tendsto h).comp hlim
  -- upper hemicontinuity: extract a convergent subsequence of couplings
  obtain ⟨γlim, hlfst, hlsnd, φ, hφmono, hφt⟩ :=
    exists_tendsto_subseq_couplings hμ hν
      (fun n => (hγs_cond n).1.1) (fun n => (hγs_cond n).1.2)
  have hγlim_C : γlim ∈ C :=
    hC.mem_of_tendsto hφt (Eventually.of_forall fun k => (hγs_cond (φ k)).2)
  have hγlim_fib : (h, γlim) ∈ FeasGraph
      (fun t x => (κμP t x : Measure (X (t + 1))))
      (fun t y => (κνP t y : Measure (Y (t + 1)))) t := ⟨hlfst, hlsnd⟩
  -- the limit is no worse: closed sublevel set of the jointly lsc F
  have hFy : F (h, γlim) ≤ y := by
    have hclosed_sub := (lowerSemicontinuous_iff_isClosed_preimage.mp hF) y
    have hpairs : Tendsto (fun k => (hs (φ k), γs (φ k))) atTop
        (𝓝 (h, γlim)) :=
      (hlim.comp hφmono.tendsto_atTop).prodMk_nhds hφt
    exact hclosed_sub.mem_of_tendsto hpairs
      (Eventually.of_forall fun k => hγs_le (φ k))
  exact le_trans (iInf₂_le γlim ⟨hγlim_fib, hγlim_C⟩) hFy

/-! ## The Bellman value functions are lower semicontinuous -/

/-- **Phase 5, V1 (BS 8.3 analogue).** For Feller kernels and lower
    semicontinuous stage costs, every Bellman value function is lower
    semicontinuous on the history space (backward induction; the
    integrand is jointly lsc by the integral pairing, the infimum by the
    Berge minimum). -/
theorem lowerSemicontinuous_VGo
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∀ k t : ℕ, LowerSemicontinuous
      (VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) k t) := by
  intro k
  induction k with
  | zero => exact fun t => hc t
  | succ k ih =>
    intro t
    have heq : VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) (k + 1) t
        = fun h => c t h + stageMin κμP κνP t
            (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
              ∂p.2.toMeasure) univ h :=
      funext fun h => VGo_succ_eq_stageMin κμP κνP c k t h
    rw [heq]
    have hFk : LowerSemicontinuous
        (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
          ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
            ∂p.2.toMeasure) := by
      have hf : LowerSemicontinuous
          (fun q : PairHist X Y t × (X (t + 1) × Y (t + 1)) =>
            VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1)
              (q.1, q.2)) := ih (t + 1)
      exact lowerSemicontinuous_lintegral_prodMk hf
    exact (hc t).add
      (lowerSemicontinuous_stageMin κμP κνP hκμ_cont hκν_cont t hFk
        isClosed_univ)

/-! ## The exact argmin correspondence -/

/-- The exact argmin correspondence: feasible one-step plans attaining
    the one-step Bellman infimum. -/
def argminSet (t : ℕ)
    (F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞)
    (h : PairHist X Y t) : Set (WeakP (X (t + 1) × Y (t + 1))) :=
  {γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
    (fun t y => (κνP t y : Measure (Y (t + 1)))) t ∧
    F (h, γ) ≤ stageMin κμP κνP t F univ h}

/-- The argmin correspondence has nonempty values: the objective attains
    its infimum on the nonempty compact fiber. -/
theorem argminSet_nonempty (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (h : PairHist X Y t) :
    (argminSet κμP κνP t F h).Nonempty := by
  obtain ⟨γ₀, hγ₀⟩ := feasGraph_fiber_nonempty' κμP κνP t h
  obtain ⟨γ, hγmem, hγmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    ⟨γ₀, hγ₀⟩ (isCompact_feasGraph_fiber κμP κνP t h)
    ((hF.comp (Continuous.prodMk continuous_const continuous_id)
      ).lowerSemicontinuousOn _)
  refine ⟨γ, hγmem, ?_⟩
  exact le_iInf₂ fun γ' hγ' => isMinOn_iff.mp hγmin γ' hγ'.1

/-- The argmin correspondence has closed values. -/
theorem isClosed_argminSet (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (h : PairHist X Y t) :
    IsClosed (argminSet κμP κνP t F h) := by
  have h1 : IsClosed {γ : WeakP (X (t + 1) × Y (t + 1)) |
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} :=
    (isCompact_feasGraph_fiber κμP κνP t h).isClosed
  have h2 : IsClosed {γ : WeakP (X (t + 1) × Y (t + 1)) |
      F (h, γ) ≤ stageMin κμP κνP t F univ h} :=
    (lowerSemicontinuous_iff_isClosed_preimage.mp
      (hF.comp (Continuous.prodMk continuous_const continuous_id))) _
  exact h1.inter h2

/-- **M1: the argmin hit-set identity.** Hitting a closed constraint set
    with an exact minimizer is equivalent to the constrained fiber being
    nonempty and the constrained value not exceeding the unconstrained
    one (attainment on the compact constrained fiber). -/
theorem argminSet_hit_eq (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    {h | (argminSet κμP κνP t F h ∩ C).Nonempty}
      = {h | ({γ | (h, γ) ∈ FeasGraph
            (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty}
        ∩ {h | stageMin κμP κνP t F C h ≤ stageMin κμP κνP t F univ h} := by
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨γ, ⟨hfib, hopt⟩, hγC⟩
    exact ⟨⟨γ, hfib, hγC⟩, le_trans (iInf₂_le γ ⟨hfib, hγC⟩) hopt⟩
  · rintro ⟨⟨γ₀, hγ₀fib, hγ₀C⟩, hle⟩
    have hcomp : IsCompact ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C) :=
      (isCompact_feasGraph_fiber κμP κνP t h).inter_right hC
    have hne' : ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty :=
      ⟨γ₀, hγ₀fib, hγ₀C⟩
    obtain ⟨γ, hγmem, hγmin⟩ := LowerSemicontinuousOn.exists_isMinOn
      hne' hcomp
      ((hF.comp (Continuous.prodMk continuous_const continuous_id)
        ).lowerSemicontinuousOn _)
    refine ⟨γ, ⟨hγmem.1, le_trans ?_ hle⟩, hγmem.2⟩
    exact le_iInf₂ fun γ' hγ' => isMinOn_iff.mp hγmin γ' ⟨hγ'.1, hγ'.2⟩

/-- The constrained-fiber hit-set against a closed target is Borel:
    transport the closed couplings hit-set (U4) along the continuous
    marginal map of the Feller model. -/
theorem measurableSet_feasGraph_fiber_hit
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    MeasurableSet {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty} := by
  have hm : Continuous (fun h : PairHist X Y t =>
      (κμP t (projX t h), κνP t (projY t h))) :=
    ((hκμ_cont t).comp (continuous_projX t)).prodMk
      ((hκν_cont t).comp (continuous_projY t))
  have hhit : IsClosed {p : ProbabilityMeasure (X (t + 1))
      × ProbabilityMeasure (Y (t + 1)) |
      ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
          = (p.1 : Measure (X (t + 1))) ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
          = (p.2 : Measure (Y (t + 1)))} :=
    isClosed_couplings_hit hC
  have hset : {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty}
      = (fun h : PairHist X Y t =>
          (κμP t (projX t h), κνP t (projY t h))) ⁻¹'
        {p : ProbabilityMeasure (X (t + 1))
            × ProbabilityMeasure (Y (t + 1)) |
          ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
              = (p.1 : Measure (X (t + 1))) ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
              = (p.2 : Measure (Y (t + 1)))} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨γ, hfib, hγC⟩
      exact ⟨γ, hγC, hfib.1, hfib.2⟩
    · rintro ⟨γ, hγC, hfst, hsnd⟩
      exact ⟨γ, ⟨hfst, hsnd⟩, hγC⟩
  rw [hset]
  exact (hhit.preimage hm).measurableSet

/-- **M2: the argmin correspondence is weakly measurable.** Hit-sets of
    open sets are Borel: decompose the open set into countably many
    closed sets; on each, compare the constrained and unconstrained
    values (both lower semicontinuous, hence Borel). -/
theorem measurableSet_argminSet_hit
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {U : Set (WeakP (X (t + 1) × Y (t + 1)))} (hU : IsOpen U) :
    MeasurableSet {h | (argminSet κμP κνP t F h ∩ U).Nonempty} := by
  obtain ⟨C, hCclosed, hUeq⟩ := hU.exists_iUnion_isClosed_of_pseudoMetrizable
  have hsplit : {h | (argminSet κμP κνP t F h ∩ U).Nonempty}
      = ⋃ n, {h | (argminSet κμP κνP t F h ∩ C n).Nonempty} := by
    rw [hUeq]
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨γ, hγa, hγU⟩
      obtain ⟨n, hγn⟩ := Set.mem_iUnion.mp hγU
      exact ⟨n, γ, hγa, hγn⟩
    · rintro ⟨n, γ, hγa, hγn⟩
      exact ⟨γ, hγa, Set.mem_iUnion.mpr ⟨n, hγn⟩⟩
  rw [hsplit]
  refine MeasurableSet.iUnion fun n => ?_
  rw [argminSet_hit_eq κμP κνP t hF (hCclosed n)]
  exact (measurableSet_feasGraph_fiber_hit κμP κνP hκμ_cont hκν_cont t
      (hCclosed n)).inter
    (measurableSet_le
      (lowerSemicontinuous_stageMin κμP κνP hκμ_cont hκν_cont t hF
        (hCclosed n)).measurable
      (lowerSemicontinuous_stageMin κμP κνP hκμ_cont hκν_cont t hF
        isClosed_univ).measurable)

/-! ## Main theorem: exact optimal measurable strategies -/

/-- **Phase 5 main theorem (BS 8.3 analogue).** In the Feller/lsc model
    there is a strategy that is pointwise feasible, EXACTLY optimal at
    every stage (time-consistent depth, ε = 0), and plain-Borel
    measurable: each stage factors through a `Measurable` map into the
    Polish space of probability measures — strictly stronger
    measurability than Phase 4's σ(Σ¹₁), under strictly stronger
    hypotheses. -/
theorem exists_optimal_measurable_strategy (T : ℕ)
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ γopt : Strat X Y,
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
            (h, z) ∂(γopt t h)
          ≤ ⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
                (fun t y => (κνP t y : Measure (Y (t + 1)))) t h),
              ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
                (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1)
                (t + 1) (h, z) ∂γm) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) := by
  have key : ∀ t : ℕ, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
      Measurable φ ∧ ∀ h, φ h ∈ argminSet κμP κνP t
        (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
          (p.1, z) ∂p.2.toMeasure) h := by
    intro t
    have hF : LowerSemicontinuous
        (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
          ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
            (p.1, z) ∂p.2.toMeasure) := by
      have hf : LowerSemicontinuous
          (fun q : PairHist X Y t × (X (t + 1) × Y (t + 1)) =>
            VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1)
              (t + 1) (q.1, q.2)) :=
        lowerSemicontinuous_VGo κμP κνP c hκμ_cont hκν_cont hc
          (T - t - 1) (t + 1)
      exact lowerSemicontinuous_lintegral_prodMk hf
    exact WeakP.exists_measurable_selection
      (fun h => argminSet_nonempty κμP κνP t hF h)
      (fun h => isClosed_argminSet κμP κνP t hF h)
      (fun U hU => measurableSet_argminSet_hit κμP κνP hκμ_cont hκν_cont
        t hF hU)
  choose φ hφmeas hφmem using key
  refine ⟨fun t h => (φ t h).toMeasure,
    fun t h => (hφmem t h).1,
    fun t h => ?_,
    fun t => ⟨φ t, hφmeas t, fun h => rfl⟩⟩
  rw [iInf_feas_eq_iInf_feasGraph _ _ (fun _ _ => inferInstance) t h]
  refine le_trans ((hφmem t h).2) ?_
  exact le_iInf₂ fun γ hγ => iInf₂_le γ ⟨hγ, Set.mem_univ γ⟩

/-! ## Exact optimality: the Bellman value is attained -/

omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)] in
/-- A stage-wise exactly optimal feasible strategy attains the Bellman
    value: `costGo = VGo` at time-consistent depths (the ε = 0 instance
    of L2 + L4; no new induction). Stated for arbitrary Markov kernels —
    Feller is not needed once the strategy exists. -/
theorem costGo_eq_VGo_of_optimal
    {κμ : (t : ℕ) → XHist X t → Measure (X (t + 1))}
    {κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1))} (T : ℕ)
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (γ : Strat X Y) (hmem : ∀ t h, γ t h ∈ Feas κμ κν t h)
    (hopt : ∀ t (h : PairHist X Y t),
      ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γ t h)
        ≤ ⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
            (_ : γm ∈ Feas κμ κν t h),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) :
    ∀ (k t : ℕ), t + k = T → ∀ h : PairHist X Y t,
      costGo c γ k t h = VGo c κμ κν k t h := by
  intro k t htk h
  refine le_antisymm ?_ (VGo_le_costGo κμ κν c γ hmem k t h)
  have hle := costGo_le_VGo_add κμ κν c T hκμ_prob γ hmem (ε := 0)
    (fun t h => by simpa using hopt t h) k t htk h
  simpa using hle

/-- **Attainment corollary.** In the Feller/lsc model the Bellman value
    is attained by a plain-Borel measurable strategy, pointwise in the
    initial history — hence also after integration against any initial
    coupling: the strategy infimum of `bellman_value_eq_multi` is a
    minimum. -/
theorem bellman_value_attained_measurable (T : ℕ)
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ γopt : Strat X Y,
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) ∧
      ∀ h₀ : PairHist X Y 0,
        costGo c γopt T 0 h₀
          = VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ := by
  obtain ⟨γopt, hmem, hopt, hφ⟩ :=
    exists_optimal_measurable_strategy κμP κνP c T hκμ_cont hκν_cont hc
  exact ⟨γopt, hmem, hφ,
    fun h₀ => costGo_eq_VGo_of_optimal c T (fun _ _ => inferInstance)
      γopt hmem hopt T 0 (by omega) h₀⟩

end MultiPeriod

end
