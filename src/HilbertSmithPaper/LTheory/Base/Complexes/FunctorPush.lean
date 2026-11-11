import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare

/-!
# Duality functors commute with pushforward

For a duality functor `(F, ξ) : ℬ → ℬ'`, a chain map `f : C ⟶ D` and `φ ∈ M(C)_n`,
`F_%(f_% φ) = (F f)_%(F_% φ)`: on the component `(p, q)` both sides are
`F(f_p) F(φ_{p,q}) F(f_q^*) ξ⁻¹ = F(f_p) F(φ_{p,q}) ξ⁻¹ (F f_q)^*`, by naturality of `ξ`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v v' u u'

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u'} [Category.{v'} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

namespace DualFunctor

private lemma ξ_inv_natural (F : DualFunctor B B') {M N : B} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Duality functors commute with pushforward.** `F_% (f_% φ) = (F f)_% (F_% φ)`. -/
lemma mapStructure_pushforward (F : DualFunctor B B') {C D : ChainComplex B ℤ} (f : C ⟶ D)
    (n : ℤ) (φ : (StructureCx C).X n) :
    F.mapStructure D n ((StructureCx.push f).f n φ) =
      (StructureCx.push ((F.toFunctor.mapHomologicalComplex _).map f)).f n
        (F.mapStructure C n φ) := by
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  rw [mapStructure_apply, StructureCx.push_apply, StructureCx.push_apply, mapStructure_apply]
  simp only [Functor.map_comp, Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, ξ_inv_natural, Category.assoc]
  simp only [Category.assoc]

end DualFunctor

end HSP
