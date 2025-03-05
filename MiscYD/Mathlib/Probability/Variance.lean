import Mathlib.Probability.Variance
import MiscYD.Mathlib.Data.ENNReal.Order
import MiscYD.Mathlib.MeasureTheory.Integral.IntegrableOn
import MiscYD.Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# TODO

Add a space before the `;` in `eVar[X; μ]`.
-/

open MeasureTheory

namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω} {s : Set Ω}

lemma evariance_congr_ae (hXY : X =ᵐ[μ] Y) : eVar[X ; μ] = eVar[Y ; μ] := by
  refine lintegral_congr_ae ?_
  filter_upwards [hXY] with ω hω
  simp [hω, integral_congr_ae hXY]

lemma variance_congr_ae (hXY : X =ᵐ[μ] Y) : Var[X ; μ] = Var[Y ; μ] := by
  simp [variance, evariance_congr_ae hXY]

@[simp] lemma evariance_zero_measure : eVar[X ; (0 : Measure[m] Ω)] = 0 := by simp [evariance]
@[simp] lemma variance_zero_measure : Var[X ; (0 : Measure[m] Ω)] = 0 := by simp [variance]

variable [IsZeroOrProbabilityMeasure μ]

-- TODO: Replace `variance_def'`
lemma variance_eq_integral_sq_sub_sq_integral (hX : MemLp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 := by
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  simp only [variance_eq_integral hX.aestronglyMeasurable.aemeasurable, sub_sq']
  rw [integral_sub, integral_add]; rotate_left
  · exact hX.integrable_sq
  · apply integrable_const
  · apply hX.integrable_sq.add
    apply integrable_const
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
  simp only [Pi.pow_apply, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul,
    Pi.mul_apply, Pi.ofNat_apply, Nat.cast_ofNat, integral_mul_right, integral_mul_left]
  ring

/-- **Variance of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then we can compute its variance as the probability
that it's equal to `0` times the conditional probability that it's equal to `1`. -/
lemma variance_of_ae_eq_zero_or_one (hXmeas : AEStronglyMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X ; μ] = (μ {ω | X ω = 0}).toReal * (μ {ω | X ω = 1}).toReal := by
  wlog hXmeas : StronglyMeasurable X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEStronglyMeasurable X μ›
    calc
      Var[X ; μ]
      _ = Var[Y ; μ] := variance_congr_ae hXY
      _ = (μ {ω | Y ω = 0}).toReal * (μ {ω | Y ω = 1}).toReal := by
        refine this hYmeas.aestronglyMeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ = (μ {ω | X ω = 0}).toReal * (μ {ω | X ω = 1}).toReal := by
        congr 2 <;> exact measure_congr <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  calc
    _ = μ[X ^ 2] - μ[X] ^ 2 :=
      variance_eq_integral_sq_sub_sq_integral <| .of_bound hXmeas.aestronglyMeasurable 1 <| by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ = μ[X] - μ[X] ^ 2 := by
      congr! 1
      exact integral_congr_ae <| by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ = (μ {ω | X ω = 0}).toReal * (μ {ω | X ω = 1}).toReal := by
      rw [sq, ← one_sub_mul, integral_of_ae_eq_zero_or_one hXmeas.aestronglyMeasurable hX]
      congr
      rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub, ← prob_compl_eq_one_sub]
      · congr 1
        refine measure_congr ?_
        filter_upwards [hX]
        -- FIXME: The following change is due to the measure theory library defeq abusing
        -- `Set Ω = (Ω → Prop)`
        change ∀ ω _, (_ ≠ _) = (_ = _)
        rintro ω (hω | hω) <;> simp [hω]
      · exact (hXmeas.measurable <| .singleton _)
      · exact prob_le_one
      · simp

end ProbabilityTheory
