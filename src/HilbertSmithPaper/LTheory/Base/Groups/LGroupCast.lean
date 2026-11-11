import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd

/-!
# Transport of L-groups along an equality of degrees

For a duality category `B` and integers `m = m'`, the transport `L_m(B) ≅ L_{m'}(B)` is the
identity isomorphism of abelian groups along the equality of degrees.

## Encoding

`LGroup.castIndex h` (the declaration of the article) is `AddEquiv.refl` after substituting
`h : m = m'`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- Transport of `L`-groups along an equality of degrees. -/
noncomputable def LGroup.castIndex {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {m m' : ℤ} (h : m = m') : LGroup B m ≃+ LGroup B m' := by
  subst h
  exact AddEquiv.refl _

end HSP
