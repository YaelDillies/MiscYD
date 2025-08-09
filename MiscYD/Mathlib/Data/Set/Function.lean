import Mathlib.Data.Set.Function

namespace Set
variable {α β : Type*} {f : α → β} {s : Set α}

@[simp] lemma surjOn_univ_unique [Unique β] : SurjOn f s univ ↔ s.Nonempty := by
  simp [univ_unique, Subsingleton.elim (f _) default, Set.Nonempty]

end Set
