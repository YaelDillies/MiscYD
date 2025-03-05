/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Exponential
import Mathlib.Probability.CondVar
import Mathlib.Topology.MetricSpace.MetricSeparated
import MiscYD.Mathlib.MeasureTheory.MeasurableSpace.Basic
import MiscYD.PhD.VCDim.HypercubeEdges

/-!
# Small VC dimension implies small variance

This file proves that each marginal of a random variable valued in a small VC dimension set family
has small conditional variance conditioned on finitely many other marginals.

## References

* *Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded
  Vapnik-Chervonenkis Dimension*, David Haussler
* Write-up by Thomas Bloom: http://www.thomasbloom.org/notes/vc.html
-/

open Fintype MeasureTheory Metric ProbabilityTheory Real
open scoped BigOperators Finset NNReal

variable {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [DecidableEq X] {A : Ω → Set X} {𝓕 : Finset (Set X)} {I : Finset X} {x : X} {d : ℕ}

-- /-- If `A` is a random variable valued in a small VC dimension set family over a fintype `X`,
-- `I ⊆ X` is finite and `x ∈ I`, then `x ∈ A`has small conditional variance conditioned on `y ∈ A`
-- for each `y ∈ I \ {x}`. -/
-- theorem small_condVar_of_isNIPWith (isNIPWith_𝓕 : IsNIPWith d 𝓕.toSet) (hA : ∀ᵐ ω ∂μ, A ω ∈ 𝓕) :
--     ∑ x ∈ I, (μ[Var[fun ω ↦ (A ω).indicator 1 x ; μ | σ(fun y : ↑(I \ {x}) ↦ y.1 ∈ A ω)]] : ℝ)
--       ≤ d :=
--   calc
--     _ = _ :=
--     _ ≤ μ[d] := _
--     _ = d := sorry
