import Mathlib.Analysis.Convex.SimplicialComplex.Basic

namespace Geometry.SimplicialComplex
variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {S : SimplicialComplex 𝕜 E} {s : Finset E}

lemma nonempty_of_mem_faces (hs : s ∈ S.faces) : s.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact S.empty_notMem hs

end Geometry.SimplicialComplex
