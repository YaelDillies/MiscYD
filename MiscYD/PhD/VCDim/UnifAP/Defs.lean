/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniformly almost periodic functions
-/

variable {E F : Set ℝ} {C D ε δ t l : ℝ} {f g : ℝ → ℂ}

variable (E l) in
/-- A set `E` of reals is **relatively dense with respect to `l`** if every (closed-open) interval
of length `l` contains an element of `E`. -/
def IsRelDenseWith : Prop := ∀ x, ∃ y ∈ Set.Ico 0 l, x + y ∈ E

lemma IsRelDenseWith.subset (hEF : E ⊆ F) : IsRelDenseWith E l → IsRelDenseWith F l :=
  forall_imp fun _x ↦ .imp fun _l ↦ .imp_right <| @hEF _

lemma IsRelDenseWith.pos (hE : IsRelDenseWith E l) : 0 < l := by
  obtain ⟨y, ⟨hy₀, hyl⟩, _⟩ := hE 0; exact hy₀.trans_lt hyl

variable (E) in
/-- A set `E` of reals is **relatively dense** if it is relatively dense with respect to some `l`.
-/
def IsRelDense : Prop := ∃ l, IsRelDenseWith E l

lemma IsRelDense.subset (hEF : E ⊆ F) : IsRelDense E → IsRelDense F := .imp fun _ ↦ .subset hEF

variable (ε t f) in
/-- A real number `t` is an **`ε`, L∞-almost period** of a function `f : ℝ \r ℝ` if
`‖f - τ t f‖_∞ ≤ ε`. -/
def IsLinftyAP : Prop := ∀ x, ‖f (x + t) - f x‖ ≤ ε

lemma IsLinftyAP.mul_fun (hfbdd : ∀ x, ‖f x‖ ≤ C) (hgbdd : ∀ x, ‖g x‖ ≤ D)
    (hf : IsLinftyAP ε t f) (hg : IsLinftyAP δ t g) : IsLinftyAP (D * ε + C * δ) t (f * g) := by
  rintro x
  have := hf x
  have := hg x
  have := hfbdd (x + t)
  have := hgbdd x
  calc
        ‖f (x + t) * g (x + t) - f x * g x‖
    _ = ‖g x * (f (x + t) - f x) + f (x + t) * (g (x + t) - g x)‖ := by ring_nf
    _ ≤ ‖g x * (f (x + t) - f x)‖ + ‖f (x + t) * (g (x + t) - g x)‖ := norm_add_le ..
    _ = ‖g x‖ * ‖f (x + t) - f x‖ + ‖f (x + t)‖ * ‖g (x + t) - g x‖ := by simp
    _ ≤ D * ε + C * δ := by gcongr <;> exact (norm_nonneg _).trans ‹_›

variable (f) in
/-- A function `f : ℝ → ℂ` is **uniformly almost periodic** if its set of `ε`, L∞-almost period is
relatively dense for all `ε > 0`. -/
def IsUnifAlmostPeriodic : Prop := ∀ ⦃ε⦄, 0 < ε → IsRelDense {t | IsLinftyAP ε t f}

/-- Any uniformly almost periodic function is uniformly continuous. -/
lemma IsUnifAlmostPeriodic.uniformContinuous (hf : IsUnifAlmostPeriodic f) :
    UniformContinuous f := sorry

/-- Any uniformly almost periodic function is bounded. -/
lemma IsUnifAlmostPeriodic.exists_forall_le (hf : IsUnifAlmostPeriodic f) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  sorry

/-- The intersection of the almost periods of two uniformly almost periodic functions is relatively
dense. -/
lemma IsUnifAlmostPeriodic.isRelDense_inter (hf : IsUnifAlmostPeriodic f)
    (hg : IsUnifAlmostPeriodic g) (hε : 0 < ε) :
    IsRelDense {t | IsLinftyAP ε t f ∧ IsLinftyAP ε t g} := sorry

lemma IsUnifAlmostPeriodic.mul (hf : IsUnifAlmostPeriodic f) (hg : IsUnifAlmostPeriodic g) :
    IsUnifAlmostPeriodic (f * g) := by
  rintro ε hε
  obtain ⟨C, hC⟩ := hf.exists_forall_le
  obtain ⟨D, hD⟩ := hg.exists_forall_le
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  replace hC x : ‖f x‖ ≤ C + 1 := (hC _).trans (by simp)
  replace hD x : ‖g x‖ ≤ D + 1 := (hD _).trans (by simp)
  refine (hf.isRelDense_inter hg (ε := ε / ((D + 1) + (C + 1))) <| by positivity).subset ?_
  rintro t ⟨htf, htg⟩
  dsimp
  convert htf.mul_fun hC hD htg
  field_simp
