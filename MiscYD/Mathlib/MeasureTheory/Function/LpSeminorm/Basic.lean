import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {p : ℝ≥0∞} {μ : Measure α}

-- TODO: Golf `MemLp.of_discrete`
@[simp] lemma MemLp.of_finite (hf : AEStronglyMeasurable f μ) [Finite α] [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hC⟩ := Finite.exists_le (‖f ·‖₊); .of_bound hf C <| .of_forall hC

end MeasureTheory
