/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Grade

/-!
### Grading a flag

A flag inherits the grading of its ambient order.
-/

open Set

variable {𝕆 α : Type*}

namespace Flag
section PartialOrder
variable [PartialOrder α] {s : Flag α}

@[simp]
lemma coe_covby_coe {a b : s} : (a : α) ⋖ b ↔ a ⋖ b := by
  refine
    and_congr_right'
      ⟨fun h c hac => h hac, fun h c hac hcb =>
        @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd => ?_⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_lt (⟨d, hd⟩ : s) a
  · exact Or.inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_lt b ⟨d, hd⟩
  · exact Or.inl (hcb.le.trans hbd)
  · cases h had hdb

@[simp]
lemma isMax_coe {a : s} : IsMax (a : α) ↔ IsMax a where
  mp h b hab := h hab
  mpr h b hab := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc ↦ ?_⟩ hab
    classical
    exact .inr <| hab.trans' <| h.isTop ⟨c, hc⟩

@[simp]
lemma isMin_coe {a : s} : IsMin (a : α) ↔ IsMin a where
  mp h b hba := h hba
  mpr h b hba := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc ↦ ?_⟩ hba
    classical
    exact .inl <| hba.trans <| h.isBot ⟨c, hc⟩

variable [Preorder 𝕆]

instance [GradeOrder 𝕆 α] (s : Flag α) : GradeOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) fun _ _ => coe_covby_coe.2

instance [GradeMinOrder 𝕆 α] (s : Flag α) : GradeMinOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covby_coe.2) fun _ => isMin_coe.2

instance [GradeMaxOrder 𝕆 α] (s : Flag α) : GradeMaxOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covby_coe.2) fun _ => isMax_coe.2

instance [GradeBoundedOrder 𝕆 α] (s : Flag α) : GradeBoundedOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covby_coe.2) (fun _ => isMin_coe.2)
    fun _ => isMax_coe.2

@[simp, norm_cast]
lemma grade_coe [GradeOrder 𝕆 α] (a : s) : grade 𝕆 (a : α) = grade 𝕆 a := rfl

end PartialOrder
end Flag
