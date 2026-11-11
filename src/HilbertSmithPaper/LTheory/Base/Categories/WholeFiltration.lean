import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration

/-!
# The whole filtration

In a duality category `ℬ`, all objects form a full additive subcategory closed under duality, and
choosing `𝒟(M) = {1_M}` for every object `M` is an involution-invariant Karoubi filtration of `ℬ`
by it.
-/

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace HSP

open DualCat

universe v u

variable (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- All objects form a full additive subcategory closed under duality. -/
instance isDualAdditive_top : IsDualAdditive (⊤ : ObjectProperty B) where
  exists_zero := ⟨0, trivial, isZero_zero B⟩
  exists_biprod {V W} _ _ := by
    have := hasBinaryBiproducts_of_finite_biproducts B
    exact ⟨BinaryBiproduct.bicone V W, ⟨BinaryBiproduct.isBilimit V W⟩, trivial⟩
  dual_mem _ := trivial

/-- **The whole filtration.** The filtration of `ℬ` by all objects, with `𝒟(M) = {1_M}`. -/
noncomputable def KaroubiFiltration.top : KaroubiFiltration (⊤ : ObjectProperty B) where
  D M := {𝟙 M}
  idem := by rintro M p rfl; simp
  split := by rintro M p rfl; exact ⟨M, trivial, 𝟙 M, 𝟙 M, by simp, by simp⟩
  split_compl := by rintro M p rfl; exact ⟨0, 0, 0, (isZero_zero B).eq_of_src _ _, by simp⟩
  nonempty M := ⟨𝟙 M, rfl⟩
  directed := by rintro M p p' rfl rfl; exact ⟨𝟙 M, rfl, by simp⟩
  factor_left g _ := ⟨𝟙 _, rfl, by simp⟩
  factor_right h _ := ⟨𝟙 _, rfl, by simp⟩
  dual_mem_iff {M} p := by
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro rfl; simp
    · intro h
      have h2 := dualHom_dualHom p
      rw [h, dualHom_id] at h2
      have h3 := congrArg (fun q => eqToHom (dual_dual M).symm ≫ q ≫ eqToHom (dual_dual M)) h2
      simpa using h3.symm

end HSP
