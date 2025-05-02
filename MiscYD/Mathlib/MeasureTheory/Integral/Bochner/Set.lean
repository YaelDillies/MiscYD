import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Notation
import MiscYD.Mathlib.MeasureTheory.Integral.IntegrableOn

open scoped ENNReal ProbabilityTheory

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {s : Set α}

-- Also in PFR
lemma integral_eq_setIntegral (hs : ∀ᵐ a ∂μ, a ∈ s) (f : α → E) :
    ∫ x, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ, ← setIntegral_congr_set]; rwa [ae_eq_univ]

end MeasureTheory

namespace MeasureTheory
variable {Ω : Type*} {m₀ m : MeasurableSpace Ω} {hm : m ≤ m₀} {X Y : Ω → ℝ} {μ : Measure[m₀] Ω}
  {s : Set Ω}

/-- **Expectation of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then its expectation is equal to the probability
that it equals `1`. -/
lemma integral_of_ae_eq_zero_or_one [IsFiniteMeasure μ] (hXmeas : AEStronglyMeasurable[m₀] X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : μ[X] = (μ {ω | X ω = 1}).toReal := by
  wlog hXmeas : StronglyMeasurable X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEStronglyMeasurable[m₀] X μ›
    calc
      μ[X]
      _ = μ[Y] := (integral_congr_ae hXY:)
      _ = (μ {ω | Y ω = 1}).toReal := by
        refine this hYmeas.aestronglyMeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ = (μ {ω | X ω = 1}).toReal := by
        congr 1
        exact measure_congr <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  calc
    _ = ∫ ω in {ω | X ω = 0 ∨ X ω = 1}, X ω ∂μ := integral_eq_setIntegral hX _
    _ = ∫ ω in {ω | X ω = 0}, X ω ∂μ + ∫ ω in {ω | X ω = 1}, X ω ∂μ := by
      rw [Set.setOf_or]
      refine setIntegral_union (by simp +contextual [Set.disjoint_left])
        (hXmeas.measurable <| .singleton 1)
        ((integrableOn_congr_fun ?_ (hXmeas.measurable <| .singleton 0)).1 integrableOn_zero)
        ((integrableOn_congr_fun ?_ (hXmeas.measurable <| .singleton 1)).1
          (integrable_const 1).integrableOn) <;>
        simp [Set.EqOn, eq_comm]
    _ = ∫ ω in {ω | X ω = 0}, 0 ∂μ + ∫ ω in {ω | X ω = 1}, 1 ∂μ := by
      congr 1
      · exact setIntegral_congr_ae (hXmeas.measurable <| .singleton 0) (by simp)
      · exact setIntegral_congr_ae (hXmeas.measurable <| .singleton 1) (by simp)
    _ = _ := by simp [Measure.real]

/-- **Expectation of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then one minus its expectation is equal to the
probability that it equals `0`. -/
lemma one_sub_integral_of_ae_eq_zero_or_one [IsProbabilityMeasure μ]
    (hXmeas : AEStronglyMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    1 - μ[X] = (μ {ω | X ω = 0}).toReal := by
  calc
    _ = μ[1 - X] := by
      rw [integral_sub' _ <| .of_bound 1 hXmeas ?_]
      · simp
      · exact integrable_const _
      · filter_upwards [hX]
        rintro ω (hω | hω) <;> simp [hω]
    _ = (μ {ω | 1 - X ω = 1}).toReal :=
      integral_of_ae_eq_zero_or_one (aestronglyMeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : ℝ))] using hX)
    _ = (μ {ω | X ω = 0}).toReal := by simp

end MeasureTheory
