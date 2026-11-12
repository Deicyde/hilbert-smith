import HilbertSmithPaper.LTheory.Base.Groups.InducedMapId
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.LTheory.Base.Groups.UnitaryInvariance

/-!
# The identity on L^p

For a duality category `A`, `(id_A)_* = id` on `L^p_k(A)`. The completion `Kar(id_A)` has duality
isomorphism `e^* = id_{(M^*, e^*)}`, so the identity maps form a unitary natural isomorphism
`id_{Kar A} ≅ Kar(id_A)`; conclude by unitary invariance and `(id_{Kar A})_* = id`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The identity maps `id_{Kar A} ≅ Kar(id_A)`, a unitary natural isomorphism. -/
private def karIdIso :
    DualFunctor.UnitaryIso (DualFunctor.id (Karoubi A)) (DualFunctor.id A).kar where
  iso := NatIso.ofComponents (fun P => Iso.refl _) (fun f => by
    erw [Category.comp_id, Category.id_comp]
    rfl)
  unitary P := by
    apply Idempotents.Karoubi.hom_ext
    change (dualHom P.p ≫ ((dualHom P.p ≫ 𝟙 _) ≫ dualHom P.p)) = dualHom P.p
    rw [Category.comp_id, ← dualHom_comp, ← dualHom_comp, P.idem, P.idem]

/-- `(id_A)_* = id` on `L^p_k(A)`. -/
theorem Lp.map_id (k : ℤ) : Lp.map (DualFunctor.id A) k = AddMonoidHom.id _ := by
  rw [Lp.map, ← LGroup.map_eq_of_unitaryIso karIdIso, LGroup.map_id]

end HSP
