import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorStructure
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorDualIso
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Base.Complexes.CycleChainMap

/-!
# Images of structures commute with the boundary, T and the duality map

For a duality functor `(F, ξ) : ℬ → ℬ'`, `F_%` commutes with `∂`, by naturality of `ξ`, and with
`T`, by `ξ_M^* = ξ_{M^*}`; and for a cycle `φ`, `(F_% φ)_♮ = F(φ_♮) ∘ ξ⁻¹`.
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

private lemma map_units_smul' {X Y : B} (u : ℤˣ) (f : X ⟶ Y) :
    F.toFunctor.map (u • f) = u • F.toFunctor.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

private lemma inv_natural' {M N : B} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

private lemma mapStructure_d' (C : ChainComplex B ℤ) (n m : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx (F.mapCx C)).d n m (F.mapStructure C n φ) =
      F.mapStructure C m ((StructureCx C).d n m φ) := by
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  change StructureCx.dHom (F.mapCx C) n m (F.mapStructure C n φ) ⟨(p, q), hpq⟩ =
    F.mapStructure C m (StructureCx.dHom C n m φ) ⟨(p, q), hpq⟩
  rw [StructureCx.dHom_apply _ _ _ _ p q hpq (n - q) (n - p) (by omega) (by omega),
    mapStructure_apply, mapStructure_apply, mapStructure_apply,
    StructureCx.dHom_apply C _ _ φ p q hpq (n - q) (n - p) (by omega) (by omega)]
  simp only [Functor.map_add, Functor.map_comp, map_units_smul', Preadditive.comp_add,
    Linear.comp_units_smul, Category.assoc, Functor.mapHomologicalComplex_obj_d]
  rw [← Category.assoc (F.ξ (C.X q)).inv (F.toFunctor.map (dualHom _)), inv_natural',
    Category.assoc]

private lemma dualHom_ξ_inv (M : B) :
    dualHom (F.ξ M).inv = (F.ξ (dual M)).inv ≫
      eqToHom ((congrArg F.toFunctor.obj (dual_dual M)).trans
      (dual_dual (F.toFunctor.obj M)).symm) := by
  have h1 : dualHom (F.ξ M).hom ≫ dualHom (F.ξ M).inv = 𝟙 _ := by
    rw [← dualHom_comp, Iso.inv_hom_id, dualHom_id]
  rw [F.ξ_dual, Category.assoc] at h1
  rw [Iso.eq_inv_comp, ← cancel_epi (eqToHom ((dual_dual (F.toFunctor.obj M)).trans
    (congrArg F.toFunctor.obj (dual_dual M)).symm)), h1]
  simp

private lemma mapStructure_T' (C : ChainComplex B ℤ) (n : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx.T (F.mapCx C)).f n (F.mapStructure C n φ) =
      F.mapStructure C n ((StructureCx.T C).f n φ) := by
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  rw [mapStructure_apply, StructureCx.T_apply, StructureCx.T_apply, mapStructure_apply]
  simp only [map_units_smul', Linear.comp_units_smul, dualHom_comp, Functor.map_comp,
    eqToHom_map, dualHom_ξ_inv, Category.assoc, eqToHom_trans]
  rw [← Category.assoc (F.ξ (C.X q)).inv, inv_natural', Category.assoc]

/-- **Images of structures commute with the boundary, T and the duality map.**
(1) `∂ (F_% φ) = F_% (∂ φ)`; (2) `T (F_% φ) = F_% (T φ)`; (3) for a cycle `φ`,
`(F_% φ)_♮ = F(φ_♮) ∘ ξ⁻¹`. -/
theorem mapStructure_compat :
    (∀ (C : ChainComplex B ℤ) (n m : ℤ) (φ : (StructureCx C).X n),
      (StructureCx (F.mapCx C)).d n m (F.mapStructure C n φ) =
        F.mapStructure C m ((StructureCx C).d n m φ)) ∧
    (∀ (C : ChainComplex B ℤ) (n : ℤ) (φ : (StructureCx C).X n),
      (StructureCx.T (F.mapCx C)).f n (F.mapStructure C n φ) =
        F.mapStructure C n ((StructureCx.T C).f n φ)) ∧
    (∀ (C : ChainComplex B ℤ) (k : ℤ) (φ : (StructureCx C).X k)
      (hφ : (StructureCx C).d k (k - 1) φ = 0)
      (hφ' : (StructureCx (F.mapCx C)).d k (k - 1) (F.mapStructure C k φ) = 0),
      StructureCx.toHom (F.mapStructure C k φ) hφ' =
        (F.dualCxIso C k).hom ≫
          (F.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).map
            (StructureCx.toHom φ hφ)) :=
  ⟨F.mapStructure_d', F.mapStructure_T', fun _ _ _ _ _ => by ext r; rfl⟩

end DualFunctor

end HSP
