import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Dual of a binary sum

In a duality category, `(M ⊕ N)^* ≅ M^* ⊕ N^*` canonically: the map to the sum has components
`ι_M^*, ι_N^*` and its inverse has components `π_M^*, π_N^*` (`HSP.DualCat.dualBiprodIso`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

namespace DualCat

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℚ C] [HasFiniteBiproducts C]
  [DualCat C] [HasBinaryBiproducts C]

/-- **The dual of a binary sum**: `(M ⊕ N)^* ≅ M^* ⊕ N^*`, with components `ι_M^*, ι_N^*`; its
inverse has components `π_M^*, π_N^*` on the summands. -/
noncomputable def dualBiprodIso (M N : C) : dual (M ⊞ N) ≅ dual M ⊞ dual N where
  hom := biprod.lift (dualHom biprod.inl) (dualHom biprod.inr)
  inv := biprod.desc (dualHom biprod.fst) (dualHom biprod.snd)
  hom_inv_id := by
    rw [biprod.lift_desc, ← dualHom_comp, ← dualHom_comp, ← dualHom_add, biprod.total,
      dualHom_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.lift_fst, biprod.lift_snd,
        Category.assoc, ← dualHom_comp, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, dualHom_id, dualHom_zero, Category.comp_id]

/-- The inverse of `dualBiprodIso` followed by `ι_M^*` is the projection onto `M^*`. -/
@[reassoc]
lemma dualBiprodIso_inv_dualHom_inl (M N : C) :
    (dualBiprodIso M N).inv ≫ dualHom biprod.inl = biprod.fst := by
  apply biprod.hom_ext'
  · rw [dualBiprodIso, biprod.inl_desc_assoc, ← dualHom_comp, biprod.inl_fst, dualHom_id,
      biprod.inl_fst]
  · rw [dualBiprodIso, biprod.inr_desc_assoc, ← dualHom_comp, biprod.inl_snd, dualHom_zero,
      biprod.inr_fst]

/-- The inverse of `dualBiprodIso` followed by `ι_N^*` is the projection onto `N^*`. -/
@[reassoc]
lemma dualBiprodIso_inv_dualHom_inr (M N : C) :
    (dualBiprodIso M N).inv ≫ dualHom biprod.inr = biprod.snd := by
  apply biprod.hom_ext'
  · rw [dualBiprodIso, biprod.inl_desc_assoc, ← dualHom_comp, biprod.inr_fst, dualHom_zero,
      biprod.inl_snd]
  · rw [dualBiprodIso, biprod.inr_desc_assoc, ← dualHom_comp, biprod.inr_snd, dualHom_id,
      biprod.inr_snd]

end DualCat

end HSP
