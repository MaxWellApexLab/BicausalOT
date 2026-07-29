/-
  Axioms Audit — machine-checked guarantee of ZERO custom axioms.

  `#print axioms` makes the Lean kernel traverse the entire dependency
  graph of each theorem. Expected output for every entry: a subset of
    [propext, Classical.choice, Quot.sound]
  — Lean 4's three foundational axioms. Any `sorry` (`sorryAx`) or
  user-declared `axiom` in the dependency graph would be listed here.
-/
import BicausalOT.Basic

-- Proposition 1
#print axioms kernel_decomp_implies_bicausal
#print axioms bicausal_implies_decomp

-- Step 2: Bellman lower bound
#print axioms V₀_le_cost_pointwise
#print axioms bellman_lower_bound

-- Step 3: ε-optimal selection / upper bound
#print axioms eps_optimal_selection
#print axioms eps_optimal_element
#print axioms eps_optimal_kernel_bound
#print axioms totalCost_le_V₀_plus_eps

-- Step 4: main theorem
#print axioms bellman_value_geq
#print axioms bellman_value_leq
#print axioms bellman_value_eq

-- Step 5: existence of optimal coupling
#print axioms optimal_kernel_exists_pointwise

-- Descriptive set theory library
#print axioms jankov_von_neumann
#print axioms LowerSemicontinuous.isLowerSemianalytic
#print axioms IsLowerSemianalytic.iInf_fiber
#print axioms Continuous.analyticallyMeasurable

-- Choquet capacitability & consequences (formerly stubbed as an axiom)
#print axioms MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact
#print axioms MeasureTheory.AnalyticSet.nullMeasurableSet
#print axioms MeasureTheory.AnalyticSet.kernel_section_gt
#print axioms lintegral_lowerSemianalytic

-- W1: the space of probability measures on a Polish space is Polish
#print axioms isTightMeasureSet_of_cauchySeq
#print axioms exists_diracMix_levyProkhorovDist_le
#print axioms ProbabilityMeasure.instPolishSpace

-- W2: Giry σ-algebra vs Borel σ-algebra of weak convergence
#print axioms probabilityMeasure_continuous_lintegral
#print axioms probabilityMeasure_borel_measurable_apply
#print axioms probabilityMeasure_borel_measurable_toMeasure

-- Giry-valued equalizer (feasibility correspondences are Borel)
#print axioms countable_generatePiSystem
#print axioms measurableSet_eq_measure

-- Multi-period Bellman recursion (general finite horizon T)
#print axioms MultiPeriod.VGo_le_costGo
#print axioms MultiPeriod.exists_eps_strategy
#print axioms MultiPeriod.costGo_le_VGo_add
#print axioms MultiPeriod.bellman_value_eq_multi

-- Lower semianalytic algebra
#print axioms IsLowerSemianalytic.add
#print axioms IsLowerSemianalytic.comp_continuous

-- History-space instances (Phase 3 plumbing)
#print axioms MultiPeriod.measurable_projX
#print axioms MultiPeriod.continuous_projX

-- Hypothesis elimination: nonemptiness of feasibility sets
#print axioms CouplingSet₀.nonempty
#print axioms FeasibleSet₀.nonempty
#print axioms MultiPeriod.Feas.nonempty
#print axioms bellman_value_eq'
#print axioms MultiPeriod.bellman_value_eq_multi'

-- Coupling sets: closed, tight, compact (unconditional existence)
#print axioms isClosed_probabilityMeasure_couplings
#print axioms isCompact_probabilityMeasure_couplings
#print axioms probabilityMeasure_couplings_nonempty

-- Lower semicontinuity of integration on P(W)
#print axioms lowerSemicontinuous_lintegral_probabilityMeasure

-- Kuratowski–Ryll-Nardzewski measurable selection
#print axioms exists_measurable_selection

-- Phase 3: semianalyticity of the Bellman value functions (BS 8.2)
#print axioms WeakP.measurable_toMeasure
#print axioms MultiPeriod.measurableSet_feasGraph
#print axioms MultiPeriod.VGo_isLowerSemianalytic

-- Phase 4: ε-optimal analytically measurable selection (BS 7.50)
#print axioms exists_fallback_selector
#print axioms exists_level_selector
#print axioms AnalyticallyMeasurable.find
#print axioms exists_eps_optimal_selector
#print axioms MultiPeriod.stageF_lowerSemianalytic
#print axioms MultiPeriod.exists_eps_strategy_analyticallyMeasurable
#print axioms MultiPeriod.bellman_value_eq_multi_measurable

-- Phase 5: couplings correspondence — upper hemicontinuity (U1–U5)
#print axioms isTightMeasureSet_range_of_tendsto
#print axioms isTightMeasureSet_couplings_of_isTightMeasureSet
#print axioms exists_tendsto_subseq_couplings
#print axioms isClosed_couplings_hit
#print axioms measurableSet_couplings_hit

-- Phase 5: the jointly lsc integral pairing (J1–J2)
#print axioms continuous_probabilityMeasure_map_prodMk
#print axioms lowerSemicontinuous_lintegral_prodMk

-- Phase 5: exact Borel-optimal strategies in the Feller/lsc model (BS 8.3)
#print axioms WeakP.exists_measurable_selection
#print axioms MultiPeriod.lowerSemicontinuous_stageMin
#print axioms MultiPeriod.lowerSemicontinuous_VGo
#print axioms MultiPeriod.argminSet_nonempty
#print axioms MultiPeriod.isClosed_argminSet
#print axioms MultiPeriod.argminSet_hit_eq
#print axioms MultiPeriod.measurableSet_argminSet_hit
#print axioms MultiPeriod.exists_optimal_measurable_strategy
#print axioms MultiPeriod.costGo_eq_VGo_of_optimal
#print axioms MultiPeriod.bellman_value_attained_measurable

-- E3-D: measurable feasible strategies in the Borel model
#print axioms MultiPeriod.measurableSet_feasGraph_fiber_hit_of_measurable
#print axioms MultiPeriod.exists_measurable_feasible_strategy
