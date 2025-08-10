/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import MiscYD.PhD.VCDim.Net

/-!
# Covering and packing numbers

This file defines covering and packing numbers of a set in a metric space.

For a set `s` in a metric space and a real number `ε > 0`:
* the `ε`-covering number of `s` is the size of a minimal `ε`-net of `s` contained in `s`.
* the `ε`-packing number of `s` is the size of a maximak `ε`-separated subset of `s`.

## References

High Dimensional Probability, Section 4.2.
-/

open scoped Finset NNReal

namespace Metric
variable {X : Type*}

/-! ### Covering number -/

section PseudoEMetricSpace
variable [PseudoEMetricSpace X] {ε : ℝ≥0} {s N : Set X} {x : X}

/-- The `ε`-covering number of a set `s` is the minimum size of an `ε`-net of `s` that is also a
subset of `s`. It is equal to `∞` if no such set exists.

If we do not require the net to be a subset of `s`, then we get a different but essentially
equivalent number: the "exterior `ε`-covering number" of `s` is at least `ecoveringNum (2 * ε) s`
and at most `ecoveringNum ε s`.

HDP 4.2.2 -/
noncomputable def ecoveringNum (ε : ℝ≥0) (s : Set X) : ℕ∞ :=
  ⨅ (N : Set X) (_ : N ⊆ s) (_ : IsNet ε s N), N.encard

/-- The `ε`-covering number of a set `s` is the minimum size of an `ε`-net of `s` that is also a
subset of `s`. It is equal to `0` if no such set exists.

If we do not require the net to be a subset of `s`, then we get a different but essentially
equivalent number: the "exterior `ε`-covering number" of `s` is at least `coveringNum (2 * ε) s`
and at most `coveringNum ε s`.

HDP 4.2.2 -/
noncomputable def coveringNum (ε : ℝ≥0) (s : Set X) : ℕ := (ecoveringNum ε s).toNat

lemma le_ecoveringNum_iff_forall_le_encard {n : ℕ∞} :
    n ≤ ecoveringNum ε s ↔ ∀ ⦃N : Set X⦄, N ⊆ s → IsNet ε s N → n ≤ N.encard := by
  simp [ecoveringNum]

lemma le_ecoveringNum_iff_forall_le_card {n : ℕ∞} :
    n ≤ ecoveringNum ε s ↔ ∀ ⦃N : Finset X⦄, N.toSet ⊆ s → IsNet ε s N → n ≤ #N  := by
  classical
  simp only [le_ecoveringNum_iff_forall_le_encard, Finset.forall, Set.Finite.coe_toFinset,
    ← Set.encard_coe_eq_coe_finsetCard]
  constructor
  · rintro h N hNfin hNs hN
    simpa [← Set.encard_coe_eq_coe_finsetCard] using h hNs hN
  · rintro h N hNs hN
    obtain hNfin | hNfin := N.finite_or_infinite
    · exact h N hNfin hNs hN
    · simp [hNfin]

lemma IsNet.ecoveringNum_le_encard (hNs : N ⊆ s) (hsN : IsNet ε s N) :
    ecoveringNum ε s ≤ N.encard := iInf₂_le_of_le N hNs <| iInf_le _ hsN

end PseudoEMetricSpace

section EMetricSpace
variable [EMetricSpace X]

@[simp] lemma ecoveringNum_zero (s : Set X) : ecoveringNum 0 s = s.encard :=
  eq_of_forall_le_iff fun n ↦ by
    simp [le_ecoveringNum_iff_forall_le_encard, ← and_imp (a := _ ⊆ s), ← subset_antisymm_iff]

@[simp] lemma coveringNum_zero (s : Set X) : coveringNum 0 s = s.ncard := by
  simp [coveringNum, Set.ncard]

end EMetricSpace

section MetricSpace
variable [MetricSpace X] [ProperSpace X] {ε : ℝ≥0} {s : Set X} {x : X}

/-- A set in a proper metric space has finite covering number iff it is relatively compact.

HDP 4.2.3.
Note that HDP 4.2.3 incorrectly claims that this holds without the `ProperSpace X` assumption, but
this can't be: If the conclusion holds true, then the closure of a closed ball (ie the closed
ball itself) should be compact since it admits a finite net (its center). -/
@[simp] lemma ecoveringNum_lt_top (hε : ε ≠ 0) : ecoveringNum ε s < ⊤ ↔ IsCompact (closure s) := by
  simp [ecoveringNum, isCompact_closure_iff_exists_finite_isNet hε]; tauto

/-- A set in a proper metric space has finite covering number iff it is relatively compact.

HDP 4.2.3.
Note that HDP 4.2.3 incorrectly claims that this holds without the `ProperSpace X` assumption, but
this can't be: If the conclusion holds true, then the closure of a closed ball (ie the closed
ball itself) should be compact since it admits a finite net (its center). -/
lemma ecoveringNum_ne_top (hε : ε ≠ 0) : ecoveringNum ε s ≠ ⊤ ↔ IsCompact (closure s) := by
  simp [ecoveringNum, isCompact_closure_iff_exists_finite_isNet hε]; tauto

/-- A set in a proper metric space has infinite covering number iff it is not relatively compact.

HDP 4.2.3.
Note that HDP 4.2.3 incorrectly claims that this holds without the `ProperSpace X` assumption, but
this can't be: If the conclusion holds true, then the closure of a closed ball (ie the closed
ball itself) should be compact since it admits a finite net (its center). -/
@[simp] lemma ecoveringNum_eq_top (hε : ε ≠ 0) : ecoveringNum ε s = ⊤ ↔ ¬ IsCompact (closure s) :=
  (ecoveringNum_ne_top hε).not_right

/-- A non-relatively compact set in a proper metric space has infinite covering number. -/
lemma ecoveringNum_eq_top_of_not_isCompact_closure (hs : ¬ IsCompact (closure s)) :
    ecoveringNum ε s = ⊤ := by
  obtain rfl | hε := eq_or_ne ε 0
  · simpa using fun hs' ↦ hs <| by simp [hs']
  · exact (ecoveringNum_eq_top hε).2 hs

end MetricSpace

/-! ### Packing number -/

section PseudoEMetricSpace
variable [PseudoEMetricSpace X] {ε : ℝ≥0} {P s : Set X} {x : X}

/-- The `ε`-packing number of a set `s` is the maximum size of an `ε`-separated of `s`. It is equal
to `∞` if no maximal `ε`-separated set exists. -/
noncomputable def epackingNum (ε : ℝ≥0) (s : Set X) : ℕ∞ :=
  ⨆ (P : Set X) (_ : P ⊆ s) (_ : IsSeparated ε P), P.encard

lemma epackingNum_le_iff_forall_encard_le {n : ℕ∞} :
    epackingNum ε s ≤ n ↔ ∀ ⦃P : Set X⦄, P ⊆ s → IsSeparated ε P → P.encard ≤ n := by
  simp [epackingNum]

lemma epackingNum_le_iff_forall_card_le {n : ℕ∞} :
    epackingNum ε s ≤ n ↔ ∀ ⦃P : Finset X⦄, P.toSet ⊆ s → IsSeparated ε P.toSet → #P ≤ n := by
  classical
  simp only [epackingNum_le_iff_forall_encard_le, Finset.forall, Set.Finite.coe_toFinset,
    ← Set.encard_coe_eq_coe_finsetCard]
  constructor
  · rintro h P hPfin hPs hP
    simpa [← Set.encard_coe_eq_coe_finsetCard] using h hPs hP
  · rintro h P hPs hP
    rw [← ENat.forall_natCast_le_iff_le]
    rintro m hm
    obtain ⟨Q, hQP, hQ⟩ := Set.exists_subset_encard_eq hm
    rw [← hQ]
    exact h _ (by simp [← Set.encard_lt_top_iff, hQ]) (hQP.trans hPs) (hP.mono hQP)

lemma IsSeparated.encard_le_epackingNum (hPs : P ⊆ s) (hP : IsSeparated ε P) :
    P.encard ≤ epackingNum ε s := le_iSup₂_of_le P hPs <| le_iSup_of_le hP le_rfl

/-- The `ε`-packing number of a set `s` is the maximum size of an `ε`-separated of `s`. It is equal
to `0` if no maximal `ε`-separated set exists. -/
noncomputable def packingNum (ε : ℝ≥0) (s : Set X) : ℕ := (epackingNum ε s).toNat

lemma exists_isSeparated_encard_eq_packingNum (hs : epackingNum ε s ≠ ⊤) :
    ∃ (N : Set X) (_ : N ⊆ s) (_ : IsSeparated ε N), N.encard = epackingNum ε s := by
  have : Nonempty ((N : Set X) ×' (_ : N ⊆ s) ×' IsSeparated ε N) := ⟨⟨∅, by simp, by simp⟩⟩
  simp [epackingNum, iSup_psigma'] at hs
  obtain ⟨⟨N, hNs, hN⟩, h⟩ := ENat.exists_eq_iSup_of_lt_top <| lt_top_iff_ne_top.2 hs
  exact ⟨N, hNs, hN, by simpa [iSup_psigma] using h⟩

/-- HDP 4.2.8 -/
lemma ecoveringNum_le_epackingNum : ecoveringNum ε s ≤ epackingNum ε s := by
  obtain hs | hs := eq_or_ne (epackingNum ε s) ⊤
  · simp [hs]
  · obtain ⟨N, hNs, hN, h⟩ := exists_isSeparated_encard_eq_packingNum hs
    simp only [← h, ne_eq, Set.encard_eq_top_iff, Set.not_infinite] at hs
    rw [← h]
    exact (IsNet.of_maximal_isSeparated <| maximal_iff_forall_gt.2 ⟨⟨hNs, hN⟩, fun M hNM ⟨hMs, hM⟩ ↦
      (hM.encard_le_epackingNum hMs).not_gt <| h ▸ hs.encard_lt_encard hNM⟩).ecoveringNum_le_encard
      hNs

/-- HDP 4.2.8 -/
lemma epackingNum_two_mul_le_ecoveringNum : epackingNum (2 * ε) s ≤ ecoveringNum ε s := by
  simp only [le_ecoveringNum_iff_forall_le_card, epackingNum_le_iff_forall_card_le, ENNReal.coe_mul,
    ENNReal.coe_ofNat, Nat.cast_le]
  rintro N hNs hN P hPs hP
  refine Finset.card_le_card_of_forall_subsingleton (edist · · ≤ ε) (fun x hx ↦ hN <| hPs hx)
    fun x hx y ⟨hy, hyx⟩ z ⟨hz, hzx⟩ ↦ hP.eq hy hz <| not_lt.2 ?_
  calc
    edist y z ≤ edist y x + edist z x := edist_triangle_right _ _ _
    _ ≤ ε + ε := by gcongr
    _ = 2 * ε := by rw [two_mul]

lemma epackingNum_le_ecoveringNum_div_two : epackingNum ε s ≤ ecoveringNum (ε / 2) s := by
  simpa [mul_div_cancel₀] using epackingNum_two_mul_le_ecoveringNum (ε := ε / 2) (s := s)

end PseudoEMetricSpace
end Metric
