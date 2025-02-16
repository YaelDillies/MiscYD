import Mathlib.Data.ENNReal.Basic

namespace ENNReal
variable {x y : ℝ≥0∞}

@[simp] lemma toNNReal_one : ENNReal.toNNReal 1 = 1 := rfl

@[simp] lemma toReal_one : ENNReal.toReal 1 = 1 := rfl

end ENNReal
