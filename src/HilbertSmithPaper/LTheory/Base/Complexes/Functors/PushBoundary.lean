import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush

/-!
# Pushforward commutes with the boundary

For a chain map `g : C ⟶ D`, `∂ (g_% x) = g_% (∂ x)` for every `x ∈ M(C)_n`: `g_%` is a chain map.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace StructureCx

/-- **Pushforward commutes with the boundary.** `∂ (g_% x) = g_% (∂ x)`. -/
lemma d_push_apply {C D : ChainComplex B ℤ} (g : C ⟶ D) (n m : ℤ) (x : (StructureCx C).X n) :
    (StructureCx D).d n m ((push g).f n x) = (push g).f m ((StructureCx C).d n m x) := by
  have := ConcreteCategory.congr_hom ((push g).comm n m) x
  simpa using this

end StructureCx

end HSP
