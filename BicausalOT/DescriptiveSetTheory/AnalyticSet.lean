/-
  Analytic Sets — re-exported from Mathlib

  Mathlib already has the full theory in:
    Mathlib.MeasureTheory.Constructions.Polish.Basic

  Key results available:
    - `MeasureTheory.AnalyticSet` (definition)
    - `MeasurableSet.analyticSet` (Borel ⊆ Analytic)
    - `AnalyticSet.image_of_continuous` (continuous image)
    - `AnalyticSet.iUnion` (countable union)
    - `AnalyticSet.iInter` (countable intersection)
    - `AnalyticSet.measurablySeparable` (Lusin separation)

  NO sorry needed — everything is already in Mathlib.
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic

-- Re-export for downstream modules
open MeasureTheory
