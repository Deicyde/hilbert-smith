import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush

/-!
# Pushforward preserves identities

`(1_C)_% = 1`: componentwise `1^* f 1 = f`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace StructureCx

/-- **Pushforward preserves identities.** `(1_C)_% = 1`. -/
lemma push_id (C : ChainComplex B ℤ) : push (𝟙 C) = 𝟙 (StructureCx C) := by
  ext n f ⟨⟨p, q⟩, hpq⟩
  change dualHom (𝟙 (C.X q)) ≫ f ⟨(p, q), hpq⟩ ≫ 𝟙 (C.X p) = f ⟨(p, q), hpq⟩
  simp

end StructureCx

end HSP
