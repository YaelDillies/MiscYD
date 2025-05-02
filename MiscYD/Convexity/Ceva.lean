/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Pi
import MiscYD.Mathlib.Analysis.Convex.Combination
import MiscYD.Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# Ceva's theorem
-/

open AffineMap Finset

variable {ι 𝕜 V : Type*} [DecidableEq ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {s t : Finset ι} {w : ι → 𝕜} {x y : ι → V} {i : ι}

-- /-- **Ceva's theorem** for affine combinations. -/
-- theorem ceva_affineComb [Nontrivial 𝕜] (hy : ∀ i ∈ s, y i ∈ affineSpan 𝕜 (x '' (s \ {i})))
--     (hs : s.Nonempty) :
--     (∃ z, ∃ c : ι → 𝕜, ∀ i ∈ s, lineMap (y i) (x i) (c i) = z) ↔
--       ∃ w : ι → 𝕜, ∑ i ∈ s, w i = 1 ∧ ∀ i ∈ s, w i ≠ 1 → (s \ {i}).centerMass w x = y i where
--   mp := by
--     rintro ⟨z, c, hz⟩
--     obtain ⟨i, hi⟩ := hs
--     norm_cast at hy
--     obtain ⟨w, hw₁, hyi⟩ := mem_affineSpan_image.1 <| hy i hi
--     refine ⟨Pi.single i (c i) + (1 - c i) • Function.update w i 0, fun j hj ↦ ?_, ?_, ?_⟩
--     · sorry

--     -- choose hc₀ hc₁ hz using hz
--     sorry
--   mpr := by
--     rintro ⟨w, hw₁, hwxy⟩
--     refine ⟨s.centerMass w x, w, fun i hi ↦ ?_⟩
--     rw [← hwxy, lineMap_centerMass_sdiff_singleton_of_ne_one hi (hw₀ _ hi) hw₁]

/-- **Ceva's theorem** for convex combinations. -/
theorem ceva_convexComb (hy : ∀ i ∈ s, y i ∈ convexHull 𝕜 (x '' (s \ {i})))
    (hs : s.Nontrivial) :
    (∃ z, ∃ c : ι → 𝕜, ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ 1 ∧ lineMap (y i) (x i) (c i) = z) ↔
      ∃ w : ι → 𝕜,
        (∀ i ∈ s, 0 ≤ w i) ∧ ∑ i ∈ s, w i = 1 ∧ ∀ i ∈ s, (s \ {i}).centerMass w x = y i where
  mp := by
    rintro ⟨z, c, hz⟩
    choose hc₀ hc₁ hz using hz
    by_cases hc : ∀ i ∈ s, c i = 1
    · refine ⟨fun _ ↦ (#s)⁻¹, by simp, by simp [hs.nonempty.card_ne_zero], fun i hi ↦ ?_⟩
      simp only [centerMass, sum_const, nsmul_eq_mul, mul_inv_rev, inv_inv, ← smul_sum, ← mul_smul,
        mul_right_comm, ne_eq, Nat.cast_eq_zero, hs.nonempty.card_ne_zero, not_false_eq_true,
        mul_inv_cancel₀, one_mul]
      sorry
      -- obtain ⟨j, hj, hji⟩ := hs.exists_ne i
    push_neg at hc
    obtain ⟨i, hi, hci⟩ := hc
    norm_cast at hy
    obtain ⟨w, hw₀, hw₁, hyi⟩ := mem_convexHull_image.1 <| hy i hi
    refine ⟨Pi.single i (c i) + (1 - c i) • Function.update w i 0, fun j hj ↦
      add_nonneg (Pi.single_nonneg (α := fun _ ↦ 𝕜).2 (hc₀ _ hi) _) <|
      mul_nonneg (sub_nonneg.2 <| hc₁ _ hi) ?_, ?_, fun j hj ↦ ?_⟩
    · obtain rfl | hji := eq_or_ne j i
      · simp
      · simpa [hji] using hw₀ _ (by simp [*])
    · simp [sum_add_distrib, hi, ← mul_sum, sum_update_of_mem, ← sum_erase_eq_sub, hw₁]
    obtain rfl | hij := eq_or_ne i j
    · rwa [centerMass_congr (w := (1 - c i) • w) (sdiff_singleton_eq_erase ..) _ fun _ _ ↦ rfl,
        centerMass_smul_left]
      · exact sub_ne_zero.2 hci.symm
      aesop
    have := (hz i hi).trans (hz j hj).symm
    simp [centerMass, sum_add_distrib]
    sorry
  mpr := by
    rintro ⟨w, hw₀, hw₁, hwxy⟩
    refine ⟨s.centerMass w x, w, fun i hi ↦ ⟨hw₀ _ hi, hw₁ ▸ single_le_sum hw₀ hi, ?_⟩⟩
    rw [← hwxy _ hi, lineMap_centerMass_sdiff_singleton_of_nonneg hi _ hw₁]
    exact fun j hj ↦ hw₀ _ <| sdiff_subset hj
