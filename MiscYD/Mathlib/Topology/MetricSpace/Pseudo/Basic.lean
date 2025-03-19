import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Metric Set

variable {X : Type*} [PseudoMetricSpace X] {s : Set X} {ε : ℝ}

/-- Any relatively compact set in a pseudometric space can be covered by finitely many balls of a
given positive radius. -/
theorem exists_finite_cover_balls_of_isCompact_closure (hs : IsCompact (closure s)) (hε : 0 < ε) :
    ∃ t ⊆ s, t.Finite ∧ s ⊆ ⋃ x ∈ t, ball x ε := by
  obtain ⟨t, hst⟩ := hs.elim_finite_subcover (fun x : s ↦ ball x ε) (fun _ ↦ isOpen_ball) fun x hx ↦
    let ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε; mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, by simp, Finset.finite_toSet _, ?_⟩
  simpa using subset_closure.trans hst
