import Mathlib.Data.ENNReal.Order
import MiscYD.Mathlib.Algebra.Order.Sub.Basic

open scoped NNReal

namespace ENNReal
variable {x y : ℝ≥0∞}

@[simp] lemma toNNReal_one : ENNReal.toNNReal 1 = 1 := rfl

@[simp] lemma toReal_one : ENNReal.toReal 1 = 1 := rfl

@[simp]
lemma toNNReal_sub (hy : y ≠ ∞) : (x - y).toNNReal = x.toNNReal - y.toNNReal := by
  lift y to ℝ≥0 using hy
  obtain rfl | hx := eq_or_ne x ∞
  · simp
  lift x to ℝ≥0 using hx
  simp [← coe_sub]

@[simp]
lemma toReal_sub (hyx : y ≤ x) (hx : x ≠ ∞) : (x - y).toReal = x.toReal - y.toReal := by
  simp [ENNReal.toReal, ne_top_of_le_ne_top hx hyx, toNNReal_mono hx hyx]

end ENNReal
