import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# Embedding into the idempotent completion

The Karoubi embedding `emb_A : A → Kar A`, `M ↦ (M, 1)`, `f ↦ f`, is Mathlib's
`CategoryTheory.Idempotents.toKaroubi`; Mathlib proves it additive and fully faithful
(`fullyFaithfulToKaroubi`). It is ℚ-linear, and `(M, 1)^* = (M^*, 1^*) = (M^*, 1)`, so it is a
strict duality functor, with `ξ` the transport along this equality.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]

instance instLinearToKaroubi : (toKaroubi A).Linear ℚ where
  map_smul _ _ := rfl

variable [HasFiniteBiproducts A] [DualCat A]

private lemma toKaroubi_dual (M : A) :
    (toKaroubi A).obj (dual M) = dual ((toKaroubi A).obj M) :=
  Idempotents.Karoubi.ext rfl (by
    change 𝟙 (dual M) ≫ 𝟙 _ = 𝟙 _ ≫ dualHom (𝟙 M)
    simp)

/-- The Karoubi embedding `A → Kar A`, `M ↦ (M, 1)`, as a duality functor whose duality
isomorphism is the identity `(M^*, 1) = (M, 1)^*`. -/
def karEmb : DualFunctor A (Karoubi A) where
  toFunctor := toKaroubi A
  ξ M := eqToIso (toKaroubi_dual A M)
  ξ_natural f := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [eqToIso.hom, Idempotents.Karoubi.comp_f, Idempotents.Karoubi.eqToHom_f]
    change dualHom f ≫ 𝟙 _ ≫ eqToHom rfl = (𝟙 _ ≫ eqToHom rfl) ≫ dualHom f
    simp)
  ξ_dual M := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [eqToIso.hom, DualCat.dualHom_eqToHom, Idempotents.Karoubi.eqToHom_f,
      eqToHom_trans])

/-- The Karoubi embedding is a strict duality functor. -/
theorem karEmb_isStrict : (karEmb A).IsStrict := fun M => ⟨toKaroubi_dual A M, rfl⟩

end HSP
