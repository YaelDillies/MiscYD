import Mathlib.Data.Set.Card

namespace Set
variable {α : Type*} {s t : Set α}

lemma Finite.encard_lt_encard' (hs : s.Finite) (h : s ⊂ t) : s.encard < t.encard :=
  (encard_mono h.subset).lt_of_ne fun he ↦ h.ne (hs.eq_of_subset_of_encard_le' h.subset he.symm.le)

attribute [simp] Set.Infinite.encard_eq

end Set
