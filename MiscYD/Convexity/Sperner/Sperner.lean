/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Sperner's lemma
-/

open Geometry Set
open scoped Affine Finset

variable {m n : ℕ}
local notation "E" => Fin (m + 1) → ℝ
variable {S : SimplicialComplex ℝ E} {f : E → Fin (m + 1)}

namespace Geometry

/-! ### Predicates -/

def IsSpernerColoring (S : SimplicialComplex ℝ E) (c : E → Fin (m + 1)) : Prop :=
  ∀ ⦃x i⦄, x ∈ S.vertices → x i = 0 → c x ≠ i

def IsPanchromatic (c : (Fin n → ℝ) → Fin (m + 1)) (X : Finset (Fin n → ℝ)) : Prop :=
  Set.SurjOn c X .univ

/-! ### Sperner's theorem itself -/

set_option linter.dupNamespace false in
private lemma strong_sperner_zero_aux {S : SimplicialComplex ℝ (Fin 1 → ℝ)}
    (hS : S.space = stdSimplex ℝ (Fin 1)) : S.faces = {{![1]}} := by
  simp +contextual only [SimplicialComplex.space, stdSimplex_unique,
    eq_singleton_iff_nonempty_unique_mem, nonempty_iUnion, convexHull_nonempty_iff,
    Finset.coe_nonempty, S.nonempty_of_mem_faces, exists_prop, and_true, mem_iUnion,
    forall_exists_index, and_imp, forall_swap (α := Fin 1 → ℝ), Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.vec_single_eq_const, Finset.eq_singleton_iff_nonempty_unique_mem, true_and] at hS ⊢
  exact ⟨hS.1, fun X hX x hx ↦ hS.2 X hX _ <| subset_convexHull _ _ hx⟩

/-- The **strong Sperner lemma**

A Sperner triangulation contains an odd number of panchromatic simplices. -/
theorem strong_sperner {S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)} {c : E → Fin (m + 1)}
    (hSspace : S.space = stdSimplex ℝ (Fin (m + 1))) (hSfin : S.faces.Finite)
    (hc : IsSpernerColoring S c) :
    Odd {s ∈ S.faces | IsPanchromatic c s}.ncard := by
  induction m with
  | zero =>
    have : ∀ s : Finset (Fin 1 → ℝ), s = {![1]} ∧ s.Nonempty ↔ s = {![1]} := by simp +contextual
    simp [IsPanchromatic, strong_sperner_zero_aux hSspace, this]
  | succ m ih =>
    sorry

set_option linter.unusedVariables false in
/-- **Sperner's lemma**

A Sperner triangulation contains some panchromatic simplex. -/
theorem sperner {S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)} {c : E → Fin (m + 1)}
    (hSspace : S.space = stdSimplex ℝ (Fin (m + 1))) (hSfin : S.faces.Finite)
    (hc : IsSpernerColoring S c) : ∃ X ∈ S.faces, IsPanchromatic f X := by
  simpa using (strong_sperner hSspace hSfin hc).pos

end Geometry
