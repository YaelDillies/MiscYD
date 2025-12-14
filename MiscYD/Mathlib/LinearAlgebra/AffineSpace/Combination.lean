import Mathlib.LinearAlgebra.AffineSpace.Combination

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    {p₀ : P} {p : ι → P} {w : ι → k} {s : Finset ι} {t : Set P}

-- TODO: Replace
lemma weightedVSub_mem_vectorSpan' (h : ∑ i ∈ s, w i = 0) (hp : ∀ i ∈ s, p i ∈ t) :
    s.weightedVSub p w ∈ vectorSpan k t := by
  obtain rfl | ⟨i, hi⟩ := s.eq_empty_or_nonempty
  · simp
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p h (p i)]
  simpa using sum_mem fun j hj ↦ Submodule.smul_mem _ _ <| vsub_mem_vectorSpan _ (hp _ hj) (hp _ hi)

-- TODO: Replace
lemma affineCombination_mem_affineSpan' [Nontrivial k] (h : ∑ i ∈ s, w i = 1)
    (hp : ∀ i ∈ s, p i ∈ t) : s.affineCombination k p w ∈ affineSpan k t := by
  classical
  have hnz : ∑ i ∈ s, w i ≠ 0 := h.symm ▸ one_ne_zero
  obtain ⟨i₀, hi₀⟩ : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
  let w1 : ι → k := Function.update (Function.const ι 0) i₀ 1
  have hw1 : ∑ i ∈ s, w1 i = 1 := by
    simp only [w1, Function.const_zero, Finset.sum_update_of_mem hi₀, Pi.zero_apply,
        Finset.sum_const_zero, add_zero]
  have hw1s : s.affineCombination k p w1 = p i₀ :=
    s.affineCombination_of_eq_one_of_eq_zero w1 p hi₀ (Function.update_self ..) fun _ _ hne =>
      Function.update_of_ne hne ..
  have hv : s.affineCombination k p w -ᵥ p i₀ ∈ (affineSpan k t).direction := by
    rw [direction_affineSpan, ← hw1s, Finset.affineCombination_vsub]
    apply weightedVSub_mem_vectorSpan' _ hp
    simp [Pi.sub_apply, h, hw1]
  rw [← vsub_vadd (s.affineCombination k p w) (p i₀)]
  exact AffineSubspace.vadd_mem_of_mem_direction hv (mem_affineSpan k <| hp _ hi₀)

lemma mem_affineSpan_image [Nontrivial k] :
    p₀ ∈ affineSpan k (p '' s) ↔
      ∃ w : ι → k, ∑ i ∈ s, w i = 1 ∧ p₀ = s.affineCombination k p w where
  mp hp := by
    classical
    rw [← Subtype.range_val (α := ι) (s := s), ← Set.range_comp] at hp
    obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    refine ⟨fun i ↦ if hi : i ∈ s then w ⟨i, hi⟩ else 0, ?_, ?_⟩
    · simp only [Finset.sum_dite, Finset.univ_eq_attach, Finset.sum_const_zero, add_zero]
      convert hw using 1
      sorry
    · sorry
  mpr := by rintro ⟨w, hw₁, rfl⟩; exact affineCombination_mem_affineSpan' hw₁ (by aesop)
