import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushComp

/-!
# Duality functors preserve sums of structures

For a duality functor `(F, ξ) : ℬ → ℬ'` and complexes `X, Y`, the canonical isomorphism
`F X ⊕ F Y ≅ F (X ⊕ Y)` carries `F_% φ ⊕ F_% ψ` to `F_% (φ ⊕ ψ)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v v' u u'

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u'} [Category.{v'} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

private lemma push_comp_apply {C D E : ChainComplex B' ℤ} (f : C ⟶ D) (g : D ⟶ E) (n : ℤ)
    (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

/-- **Duality functors preserve sums of structures.** The inverse of the canonical isomorphism
`F (X ⊕ Y) ≅ F X ⊕ F Y` carries `F_% φ ⊕ F_% ψ` to `F_% (φ ⊕ ψ)`. -/
lemma DualFunctor.mapStructure_sum (F : DualFunctor B B') (X Y : ChainComplex B ℤ) (n : ℤ)
    (φ : (StructureCx X).X n) (ψ : (StructureCx Y).X n) :
    (StructureCx.push ((F.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).mapBiprod
      X Y).inv).f n (StructureCx.sum (F.mapStructure X n φ) (F.mapStructure Y n ψ)) =
      F.mapStructure (X ⊞ Y) n (StructureCx.sum φ ψ) := by
  unfold StructureCx.sum
  rw [Functor.mapBiprod_inv, map_add, map_add, ← push_comp_apply, ← push_comp_apply,
    biprod.inl_desc, biprod.inr_desc, DualFunctor.mapStructure_pushforward,
    DualFunctor.mapStructure_pushforward]

end HSP
