import Mathlib.Data.Finset.SDiff

namespace Finset
variable {α : Type*} [DecidableEq α] {s : Finset α} {a : α}

@[simp] lemma insert_sdiff_self_of_mem (ha : a ∈ s) : insert a (s \ {a}) = s := by ext; grind

end Finset
