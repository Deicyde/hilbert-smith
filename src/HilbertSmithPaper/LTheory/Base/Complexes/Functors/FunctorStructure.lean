import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorComplex
import HilbertSmithPaper.LTheory.Base.Complexes.StructureComplex

/-!
# Image of structures under a duality functor

For a duality functor `(F, ξ) : ℬ → ℬ'`, `F_% : M(C)_n → M(F C)_n` sends `φ` to
`(F_% φ)_{r,s} = F(φ_{r,s}) ∘ ξ⁻¹_{C_s}`. It is ℚ-linear.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {B' : Type u₂} [Category.{v₂} B'] [Preadditive B'] [Linear ℚ B'] [HasFiniteBiproducts B']
  [DualCat B']

namespace DualFunctor

variable (F : DualFunctor B B')

/-- `F_%` on families of maps: `(F_% φ)_{r,s} = ξ⁻¹_{C_s} ≫ F(φ_{r,s})`. -/
private def mapStructureHom (C : ChainComplex B ℤ) (n : ℤ) :
    (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1) →ₗ[ℚ]
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n},
        dual ((F.mapCx C).X x.1.2) ⟶ (F.mapCx C).X x.1.1) where
  toFun φ x := (F.ξ (C.X x.1.2)).inv ≫ F.toFunctor.map (φ x)
  map_add' φ ψ := by
    funext x
    simp only [Pi.add_apply, Functor.map_add, Preadditive.comp_add]
  map_smul' c φ := by
    funext x
    simp only [Pi.smul_apply, Functor.Linear.map_smul, Linear.comp_smul, RingHom.id_apply]

/-- **Image of structures under a duality functor.** `F_% : M(C)_n → M(F C)_n`,
`(F_% φ)_{r,s} = F(φ_{r,s}) ∘ ξ⁻¹_{C_s}`. (It commutes with `∂`; it is not a morphism of complexes
in Lean only because `M(C)` and `M(F C)` are complexes of ℚ-vector spaces in possibly different
universes.) -/
def mapStructure (C : ChainComplex B ℤ) (n : ℤ) :
    (StructureCx C).X n →ₗ[ℚ] (StructureCx (F.mapCx C)).X n :=
  F.mapStructureHom C n

/-- The defining equation of `F_%`. -/
lemma mapStructure_apply (C : ChainComplex B ℤ) (n : ℤ) (φ : (StructureCx C).X n) (p q : ℤ)
    (h : p + q = n) :
    (F.mapStructure C n φ) ⟨(p, q), h⟩ = (F.ξ (C.X q)).inv ≫ F.toFunctor.map (φ ⟨(p, q), h⟩) :=
  rfl

end DualFunctor

end HSP
