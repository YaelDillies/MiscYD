import Mathlib.Probability.CondVar
import MiscYD.Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory

namespace ProbabilityTheory
variable {Ω : Type*} {m₀ m m' : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure[m₀] Ω}
  [IsFiniteMeasure μ] {s : Set Ω}

/-- **Conditional variance of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then we can compute its conditional variance as the
conditional probability that it's equal to `0` times the conditional probability that it's equal to
`1`. -/
lemma condVar_of_ae_eq_zero_or_one (hm : m ≤ m₀) (hXmeas : AEStronglyMeasurable[m₀] X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X ; μ | m] =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
  wlog hXmeas : StronglyMeasurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEStronglyMeasurable[m₀] X μ›
    calc
      Var[X ; μ | m]
      _ =ᵐ[μ] Var[Y ; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aestronglyMeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
        refine .mul ?_ ?_ <;>
          exact condExp_congr_ae <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  calc
    _ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
      condVar_ae_eq_condExp_sq_sub_sq_condExp hm <| .of_bound hXmeas.aestronglyMeasurable 1 <| by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] - μ[X | m] ^ 2 := by
      refine .sub ?_ ae_eq_rfl
      exact condExp_congr_ae <| by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
      rw [sq, ← one_sub_mul, mul_comm]
      refine .mul ae_eq_rfl ?_
      calc
        1 - μ[X | m]
        _ = μ[1 | m] - μ[X | m] := by simp [Pi.one_def, hm]
        _ =ᵐ[μ] μ[1 - X | m] := by
          refine (condExp_sub (integrable_const _)
            (.of_bound 1 hXmeas.aestronglyMeasurable ?_) _).symm
          filter_upwards [hX]
          rintro ω (hω | hω) <;> simp [hω]

end ProbabilityTheory
