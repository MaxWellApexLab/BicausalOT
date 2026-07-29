/-
  AxiomAudit — headline-theorem axiom audit for external verification.

  Run from the repository root AFTER building the library:

    lake exe cache get
    lake build
    lake env lean AxiomAudit.lean

  Expected output: four reports, each listing ONLY Lean's three standard
  foundational axioms

    [propext, Classical.choice, Quot.sound]

  Any other entry (in particular `sorryAx`, or any user-declared axiom)
  constitutes a FAILURE of the audit.

  (The full per-theorem audit of the whole library — 75 entries — runs
  automatically as part of `lake build` via BicausalOT/AxiomsAudit.lean;
  this file is the four-headline external check.)
-/
import BicausalOT.Basic

-- 1. Jankov–von Neumann uniformization of analytic sets (Kechris 18.1)
#print axioms jankov_von_neumann

-- 2. Kuratowski–Ryll-Nardzewski measurable selection (Kechris 12.13)
#print axioms exists_measurable_selection

-- 3. Choquet capacitability for analytic sets (Kechris 30.13 / BS 7.42)
#print axioms MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact

-- 4. W1: the space of probability measures on a Polish space is Polish
#print axioms ProbabilityMeasure.instPolishSpace
