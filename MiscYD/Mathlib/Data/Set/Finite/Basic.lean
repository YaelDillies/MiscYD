import Mathlib.Data.Set.Finite.Basic

namespace Finset
variable {α : Type*}

lemma «forall» {p : Finset α → Prop} :
    (∀ s, p s) ↔ ∀ (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp h s hs := h _
  mpr h s := by simpa using h s s.finite_toSet

lemma «exists» {p : Finset α → Prop} :
    (∃ s, p s) ↔ ∃ (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp := fun ⟨s, hs⟩ ↦ ⟨s, s.finite_toSet, by simpa⟩
  mpr := fun ⟨s, hs, hs'⟩ ↦ ⟨hs.toFinset, hs'⟩

end Finset
