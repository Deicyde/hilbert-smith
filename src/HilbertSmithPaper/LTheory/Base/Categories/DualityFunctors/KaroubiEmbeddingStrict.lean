import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor

/-!
# The Karoubi embedding is strict

The Karoubi embedding `emb_A : A → Kar A` is a strict duality functor:
`(M^*, 1) = (M, 1)^*`, and `ξ_M` is the transport along this equality.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The Karoubi embedding is a strict duality functor. -/
theorem karEmb_isStrict : (karEmb A).IsStrict := fun M =>
  ⟨Idempotents.Karoubi.ext rfl (by
    change 𝟙 (dual M) ≫ 𝟙 _ = 𝟙 _ ≫ dualHom (𝟙 M)
    simp), rfl⟩

end HSP
