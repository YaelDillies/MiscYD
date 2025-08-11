/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic

/-!
# VCₙ dimension of convex sets in ℝⁿ⁺¹, ℝⁿ⁺²

In the literature it is known that every convex set in ℝ² has VC dimension at most 3,
and there exists a convex set in ℝ³ with infinite VC dimension (even more strongly,
which shatters an infinite set).

This file proves that every convex set in ℝⁿ has finite VCₙ dimension, constructs a convex set in
ℝⁿ⁺² with infinite VCₙ dimension (even more strongly, which n-shatters an infinite set),
and conjectures that every convex set in ℝⁿ⁺¹ has finite VCₙ dimension.
-/

/-! ### What's known -/

/-- Every convex set in ℝ² has VC dimension at most 3. -/
lemma vc_lt_four_of_convex_r2 {C : Set (Fin 2 → ℝ)} (hC : Convex ℝ C)
    {x : Fin 4 → Fin 2 → ℝ} {y : Set (Fin 4) → Fin 2 → ℝ}
    (hxy : ∀ i s, x i + y s ∈ C ↔ i ∈ s) : False := sorry

/-- There exists a set of infinite VC dimension in ℝ³. -/
lemma exists_convex_r3_vc_eq_infty :
    ∃ (C : Set (Fin 3 → ℝ)) (hC : Convex ℝ C) (x : ℕ → Fin 3 → ℝ) (y : Set ℕ → Fin 3 → ℝ),
      ∀ i s, x i + y s ∈ C ↔ i ∈ s := sorry

/-! ### What's new -/

/-- There exists a set of infinite VCₙ dimension in ℝⁿ⁺². -/
lemma exists_convex_rn_add_two_vc_n_eq_infty (n : ℕ) :
    ∃ (C : Set (Fin (n + 2) → ℝ)) (hC : Convex ℝ C) (x : Fin n → ℕ → Fin (n + 2) → ℝ)
      (y : Set (Fin n → ℕ) → Fin (n + 2) → ℝ),
        ∀ i s, ∑ k, x k (i k) + y s ∈ C ↔ i ∈ s := sorry

/-! ### Conjectures -/

/-- Every convex set in ℝ³ has VC₂ dimension at most 1.

In fact, this set n-shatters an infinite set. -/
lemma vc2_lt_two_of_convex_r3 {C : Set (Fin 3 → ℝ)} (hC : Convex ℝ C)
    {x y : Fin 2 → Fin 3 → ℝ} {z : Set (Fin 2 × Fin 2) → Fin 3 → ℝ}
    (hxy : ∀ i j s, x i + y j + z s ∈ C ↔ (i, j) ∈ s) : False := sorry

/-- Every convex set in ℝⁿ⁺¹ has VC₂ dimension at most 1. -/
lemma exists_vcn_le_of_convex_rn_add_one (n : ℕ) :
    ∃ d : ℕ, ∀ (C : Set (Fin (n + 1) → ℝ)) (hC : Convex ℝ C) (x : Fin n → ℕ → Fin (n + 1) → ℝ)
      (y : Set (Fin n → ℕ) → Fin (n + 1) → ℝ) (hxy : ∀ i s, ∑ k, x k (i k) + y s ∈ C ↔ i ∈ s),
        False := sorry
