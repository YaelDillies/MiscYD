import Mathlib.Data.ENat.Lattice

namespace ENat

lemma forall_ge_iff_eq_top {n : ℕ∞} : (∀ a : ℕ, a ≤ n) ↔ n = ⊤ := WithTop.forall_ge_iff_eq_top

-- TODO: Generalise to `WithTop`
lemma forall_natCast_le_iff_le {m n : ℕ∞} : (∀ a : ℕ, a ≤ m → a ≤ n) ↔ m ≤ n := by
  obtain _ | m := m
  · simp [WithTop.none_eq_top, forall_ge_iff_eq_top]
  · exact ⟨fun h ↦ h _ le_rfl, fun hmn a ham ↦ ham.trans hmn⟩

end ENat
