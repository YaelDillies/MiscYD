import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
## TODO

Introduce `HasFiniteIntegralOn`?
-/

open scoped ENNReal

namespace MeasureTheory
variable {α E : Type*} {mα : MeasurableSpace α}

alias HasFiniteIntegral.restrict_of_bound := hasFiniteIntegral_restrict_of_bounded
alias HasFiniteIntegral.of_bound := hasFiniteIntegral_of_bounded

variable [NormedAddCommGroup E] {f : α → E} {s : Set α} {μ : Measure α} (C : ℝ)

lemma Integrable.of_bound [IsFiniteMeasure μ] (hf : AEStronglyMeasurable f μ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable f μ := ⟨hf, .of_bound hfC⟩

lemma IntegrableOn.of_bound (hs : μ s < ∞) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hfC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : IntegrableOn f s μ := ⟨hf, .restrict_of_bound hs hfC⟩

end MeasureTheory
