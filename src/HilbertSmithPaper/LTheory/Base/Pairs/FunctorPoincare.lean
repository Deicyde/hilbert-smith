import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex

/-!
# Duality functors carry Poincaré complexes

A duality functor `(F, ξ) : B → B'` sends a strict `k`-dimensional symmetric Poincaré complex
`(C, φ)` to `(F C, F_% φ)` with `(F_% φ)_{r,s} = F(φ_{r,s}) ∘ ξ⁻¹_{C_s}`. The proof
obligations are:

1. `F_%` is a chain map `M(C) ⟶ M(F C)` (`DualFunctor.mapStructure`), by naturality of `ξ`, and
   commutes with `T` (`DualFunctor.mapStructure_T`), by `ξ_M^* = ξ_{M^*}`;
2. `F` preserves zero objects;
3. `(F_% φ)_♮ = F(φ_♮) ∘ ξ⁻¹`, where `ξ⁻¹ : (F C)^{k-*} ≅ F(C^{k-*})`
   (`DualFunctor.dualCxIso`) is an isomorphism of complexes, and `F` preserves chain homotopy
   equivalences (Mathlib's `Functor.mapHomotopyEquiv`).

For strict `F`, `ξ` is an identity, so `F_% φ = F φ` up to these identifications.
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

/-- The image `F C` of a complex under a duality functor. -/
abbrev mapCx (C : ChainComplex B ℤ) : ChainComplex B' ℤ :=
  (F.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).obj C

private lemma map_units_smul' {X Y : B} (u : ℤˣ) (f : X ⟶ Y) :
    F.toFunctor.map (u • f) = u • F.toFunctor.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

private lemma inv_natural' {M N : B} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- `F_%` on `M(C)_n`: `(F_% φ)_{r,s} = ξ⁻¹_{C_s} ≫ F(φ_{r,s})`. -/
def mapStructureHom (C : ChainComplex B ℤ) (n : ℤ) :
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

/-- `F_% : M(C)_n → M(F C)_n`, `(F_% φ)_{r,s} = F(φ_{r,s}) ∘ ξ⁻¹_{C_s}`. (It commutes with `∂`,
`DualFunctor.mapStructure_d`; it is not a morphism of complexes in Lean only because `M(C)` and
`M(F C)` are complexes of ℚ-vector spaces in possibly different universes.) -/
def mapStructure (C : ChainComplex B ℤ) (n : ℤ) :
    (StructureCx C).X n →ₗ[ℚ] (StructureCx (F.mapCx C)).X n :=
  F.mapStructureHom C n

/-- `F_%` commutes with `∂`. -/
lemma mapStructure_d (C : ChainComplex B ℤ) (n m : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx (F.mapCx C)).d n m (F.mapStructure C n φ) =
      F.mapStructure C m ((StructureCx C).d n m φ) := by
  obtain ⟨φ, rfl⟩ : ∃ ψ : (∀ x : {x : ℤ × ℤ // x.1 + x.2 = n}, dual (C.X x.1.2) ⟶ C.X x.1.1),
    ψ = φ := ⟨φ, rfl⟩
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  change StructureCx.dHom (F.mapCx C) n m (F.mapStructureHom C n φ) ⟨(p, q), hpq⟩ =
    F.mapStructureHom C m (StructureCx.dHom C n m φ) ⟨(p, q), hpq⟩
  rw [StructureCx.dHom_apply _ _ _ _ p q hpq (n - q) (n - p) (by omega) (by omega)]
  simp only [mapStructureHom, LinearMap.coe_mk, AddHom.coe_mk]
  rw [StructureCx.dHom_apply C _ _ φ p q hpq (n - q) (n - p) (by omega) (by omega)]
  simp only [Functor.map_add, Functor.map_comp, map_units_smul', Preadditive.comp_add,
    Linear.comp_units_smul, Category.assoc, Functor.mapHomologicalComplex_obj_d]
  rw [← Category.assoc (F.ξ (C.X q)).inv (F.toFunctor.map (dualHom _)), inv_natural',
    Category.assoc]

lemma mapStructure_apply (C : ChainComplex B ℤ) (n : ℤ) (φ : (StructureCx C).X n) (p q : ℤ)
    (h : p + q = n) :
    (F.mapStructure C n φ) ⟨(p, q), h⟩ = (F.ξ (C.X q)).inv ≫ F.toFunctor.map (φ ⟨(p, q), h⟩) :=
  rfl

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

/-- `F_%` commutes with `T`. -/
lemma mapStructure_T (C : ChainComplex B ℤ) (n : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx.T (F.mapCx C)).f n (F.mapStructure C n φ) =
      F.mapStructure C n ((StructureCx.T C).f n φ) := by
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  rw [mapStructure_apply, StructureCx.T_apply, StructureCx.T_apply, mapStructure_apply]
  simp only [map_units_smul', Linear.comp_units_smul, dualHom_comp, Functor.map_comp,
    eqToHom_map, dualHom_ξ_inv, Category.assoc, eqToHom_trans]
  rw [← Category.assoc (F.ξ (C.X q)).inv, inv_natural', Category.assoc]

/-- For strict `F`, `F_% φ = F φ`: each component is `F(φ_{r,s})` precomposed with the
identification `(F C_s)^* = F(C_s^*)`. -/
lemma mapStructure_apply_of_isStrict (hF : F.IsStrict) (C : ChainComplex B ℤ) (n : ℤ)
    (φ : (StructureCx C).X n) (p q : ℤ) (h : p + q = n) :
    ∃ e : dual (F.toFunctor.obj (C.X q)) = F.toFunctor.obj (dual (C.X q)),
      (F.mapStructure C n φ) ⟨(p, q), h⟩ = eqToHom e ≫ F.toFunctor.map (φ ⟨(p, q), h⟩) := by
  obtain ⟨e, he⟩ := hF (C.X q)
  refine ⟨e.symm, ?_⟩
  have hinv : (F.ξ (C.X q)).inv = eqToHom e.symm := by
    rw [← cancel_epi (F.ξ (C.X q)).hom, Iso.hom_inv_id, he, eqToHom_trans, eqToHom_refl]
  rw [mapStructure_apply, hinv]

/-- The isomorphism `ξ⁻¹ : (F C)^{k-*} ≅ F(C^{k-*})`, `ξ⁻¹_{C_{k-r}}` in degree `r`. -/
def dualCxIso (C : ChainComplex B ℤ) (k : ℤ) : dualCx (F.mapCx C) k ≅ F.mapCx (dualCx C k) :=
  HomologicalComplex.Hom.isoOfComponents (fun r => (F.ξ (C.X (k - r))).symm) (by
    intro i j _
    simp only [Iso.symm_hom, Functor.mapHomologicalComplex_obj_d, map_units_smul',
      Linear.comp_units_smul, Linear.units_smul_comp, inv_natural'])

lemma toHom_mapStructure (C : ChainComplex B ℤ) (k : ℤ) (φ : (StructureCx C).X k)
    (hφ : (StructureCx C).d k (k - 1) φ = 0)
    (hφ' : (StructureCx (F.mapCx C)).d k (k - 1) (F.mapStructure C k φ) = 0) :
    StructureCx.toHom (F.mapStructure C k φ) hφ' =
      (F.dualCxIso C k).hom ≫
        (F.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)).map (StructureCx.toHom φ hφ) := by
  ext r
  rfl

end DualFunctor

namespace SymPoincare

/-- The image `(F C, F_% φ)` of a strict `k`-dimensional symmetric Poincaré complex under a
duality functor `(F, ξ)`, with `(F_% φ)_r = F(φ_r) ∘ ξ⁻¹_{C_{k-r}}`. -/
@[simps]
noncomputable def map (F : DualFunctor B B') {k : ℤ} (x : SymPoincare B k) : SymPoincare B' k where
  C := F.mapCx x.C
  φ := F.mapStructure x.C k x.φ
  bounded r hr := F.toFunctor.map_isZero (x.bounded r hr)
  cycle := by rw [F.mapStructure_d, x.cycle, map_zero]
  symmetric := by rw [F.mapStructure_T, x.symmetric]
  poincare := by
    obtain ⟨e, he⟩ := x.poincare
    refine ⟨(HomotopyEquiv.ofIso (F.dualCxIso x.C k)).trans (F.toFunctor.mapHomotopyEquiv e), ?_⟩
    rw [F.toHom_mapStructure x.C k x.φ x.cycle, ← he]
    rfl

end SymPoincare

end HSP
