/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Exponential
import MiscYD.Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import MiscYD.PhD.VCDim.SmallVCImpSmallCondVar
import MiscYD.PhD.VCDim.CoveringPacking

/-!
# Haussler's packing lemma

This file proves Haussler's packing lemma, which is the statement that an `ε`-separated set family
of VC dimension at most `d` over finitely many elements has size at most `(Cε⁻¹) ^ d` for some
absolute constant `C`.

## References

* *Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded
  Vapnik-Chervonenkis Dimension*, David Haussler
* Write-up by Thomas Bloom: http://www.thomasbloom.org/notes/vc.html
* High Dimensional Probability 8.3.18
-/

open Fintype MeasureTheory Metric Real
open scoped Finset ENNReal NNReal

namespace SetFamily
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ} [Fact (1 ≤ p)] {ε : ℝ≥0} {k d : ℕ}

noncomputable def dimensionReductionConst (ε : ℝ) (𝓕 : Finset (Lp ℝ 2 μ)) : ℝ :=
  ε ^ (-4 : ℝ) * log #𝓕

-- lemma dimensionReductionConst_nonneg (hε )

lemma dimension_reduction {𝓕 : Finset (Lp ℝ 2 μ)} (isSeparated_𝓕 : IsSeparated ε 𝓕.toSet) :
    ∃ μ₀ : Measure Ω, {ω | μ₀ {ω} ≠ 0}.ncard ≤ dimensionReductionConst ε 𝓕 ∧ sorry := sorry

def hausslerPackingConst : ℕ := sorry

/-- The **Haussler packing lemma**. -/
theorem haussler_packing_card_isSeparated {𝓕 : Finset (Lp ℝ 2 μ)}
    (ae_eq_zero_or_one_of_mem_𝓕 : ∀ A ∈ 𝓕, ∀ᵐ ω ∂ μ, A ω = 0 ∨ A ω = 1)
    (isNIPWith_𝓕 : IsNIPWith d <| (fun A : Lp ℝ 2 μ ↦ ⇑A ⁻¹' {1}) '' 𝓕.toSet)
    (isSeparated_𝓕 : IsSeparated ε 𝓕.toSet) :
    #𝓕 ≤ (2 / ε) ^ (hausslerPackingConst * d) :=
  sorry

/-- The **Haussler packing lemma**. -/
theorem haussler_packing_epackingNum {𝓕 : Set (Lp ℝ 2 μ)} (hε : ε ≠ 0)
    (ae_eq_zero_or_one_of_mem_𝓕 : ∀ A ∈ 𝓕, ∀ᵐ ω ∂ μ, A ω = 0 ∨ A ω = 1)
    (isNIPWith_𝓕 : IsNIPWith d <| (fun A : Lp ℝ 2 μ ↦ ⇑A ⁻¹' {1}) '' 𝓕) :
    epackingNum ε 𝓕 ≤ (2 / ε : ℝ≥0∞) ^ (hausslerPackingConst * d) := by
  refine coe_epackingNum_le_iff_forall_card_le.2 fun 𝓟 h𝓟𝓕 h𝓟 ↦ ?_
  have := haussler_packing_card_isSeparated (fun A hA ↦ ae_eq_zero_or_one_of_mem_𝓕 _ <| h𝓟𝓕 hA)
    (isNIPWith_𝓕.anti <| Set.image_subset _ <| h𝓟𝓕) h𝓟
  rw [← ENNReal.coe_le_coe] at this
  push_cast at this
  rwa [ENNReal.coe_div hε] at this

end SetFamily
