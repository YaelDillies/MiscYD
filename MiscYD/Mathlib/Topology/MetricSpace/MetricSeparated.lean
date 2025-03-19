import Mathlib.Topology.MetricSpace.MetricSeparated

open Set
open scoped ENNReal

namespace Metric
variable {X : Type*} [PseudoEMetricSpace X] {ε δ : ℝ≥0∞} {s t : Set X} {x : X}

/-- A set `s` is `ε`-separated if its elements are pairwise at distance at least `ε` from each
other. -/
def IsSeparated (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε < edist · ·)

@[simp] protected nonrec lemma IsSeparated.empty : IsSeparated ε (∅ : Set X) := pairwise_empty _
@[simp] protected nonrec lemma IsSeparated.singleton : IsSeparated ε {x} := pairwise_singleton ..

@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated ε s := hs.pairwise _

alias _root_.Set.Subsingleton.isSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.anti (hεδ : ε ≤ δ) (hs : IsSeparated δ s) : IsSeparated ε s :=
  hs.mono' fun _ _ ↦ hεδ.trans_lt

lemma IsSeparated.subset (hst : s ⊆ t) (hs : IsSeparated ε t) : IsSeparated ε s := hs.mono hst

protected lemma IsSeparated.insert (hs : IsSeparated ε s) (h : ∀ y ∈ s, x ≠ y → ε < edist x y) :
    IsSeparated ε (insert x s) := hs.insert_of_symmetric (fun _ _ ↦ by simp [edist_comm]) h

end Metric
