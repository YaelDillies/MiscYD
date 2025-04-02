import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.ENatENNReal

/-!
# TODO

This file is not about `Real`!
-/

open scoped ENNReal

namespace ENat
variable {ι : Sort*}

@[simp] lemma toENNReal_iSup (f : ι → ℕ∞) : ↑(⨆ i, f i) = ⨆ i, (f i : ℝ≥0∞) := by
  refine eq_of_forall_ge_iff fun r ↦ ?_
  simp
  sorry

@[simp] lemma toENNReal_iInf (f : ι → ℕ∞) : ↑(⨅ i, f i) = ⨅ i, (f i : ℝ≥0∞) := by
  refine eq_of_forall_le_iff fun r ↦ ?_
  simp
  sorry

end ENat
