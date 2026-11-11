import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor

/-!
# Duality functors carry pairs to pairs

A duality functor `(F, ξ) : B → B'` sends a strict `n`-dimensional Poincaré pair
`(f : C ⟶ D, δφ, φ)` to `(F f : F C ⟶ F D, F_% δφ, F_% φ)`. The boundary conditions are those of
`SymPoincare.map`; `F_%` commutes with `T`, with `∂` and with pushforward along `f`
; and the pair map of the image is `κ ∘ F(ψ) ∘ ξ⁻¹`, with
`κ : F(𝒞(f)) ≅ 𝒞(F f)` the canonical isomorphism , so it is a chain
homotopy equivalence. For a duality functor `A → A'` this is applied to `Kar F`.
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

private lemma map_units_smul'' {X Y : B} (u : ℤˣ) (f : X ⟶ Y) :
    F.toFunctor.map (u • f) = u • F.toFunctor.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

private lemma inv_natural'' {M N : B} (f : M ⟶ N) :
    (F.ξ N).inv ≫ F.toFunctor.map (dualHom f) = dualHom (F.toFunctor.map f) ≫ (F.ξ M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← F.ξ_natural, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- `F_%` commutes with pushforward: `F_% (f_% φ) = (F f)_% (F_% φ)`. -/
lemma mapStructure_push {C D : ChainComplex B ℤ} (f : C ⟶ D) (n : ℤ) (φ : (StructureCx C).X n) :
    F.mapStructure D n ((StructureCx.push f).f n φ) =
      (StructureCx.push ((F.toFunctor.mapHomologicalComplex _).map f)).f n
        (F.mapStructure C n φ) := by
  refine funext fun x => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := x
  rw [mapStructure_apply, StructureCx.push_apply, StructureCx.push_apply, mapStructure_apply]
  simp only [Functor.map_comp, Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, inv_natural'', Category.assoc]
  simp only [Category.assoc]

/-- `F(X ⊞ Y) ≅ F X ⊞ F Y` for the additive functor `F`. -/
private noncomputable def biprodIso (X Y : B) :
    F.toFunctor.obj (X ⊞ Y) ≅ F.toFunctor.obj X ⊞ F.toFunctor.obj Y where
  hom := biprod.lift (F.toFunctor.map biprod.fst) (F.toFunctor.map biprod.snd)
  inv := biprod.desc (F.toFunctor.map biprod.inl) (F.toFunctor.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.toFunctor.map_comp, ← F.toFunctor.map_comp, ← F.toFunctor.map_add,
      biprod.total, F.toFunctor.map_id]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [← F.toFunctor.map_comp]

/-- The canonical isomorphism `κ : F(𝒞(f)) ≅ 𝒞(F f)`, `F(D_r ⊞ C_{r-1}) ≅ F D_r ⊞ F C_{r-1}`. -/
private noncomputable def mapConeIso {C D : ChainComplex B ℤ} (f : C ⟶ D) :
    F.mapCx (cone f) ≅ cone ((F.toFunctor.mapHomologicalComplex _).map f) :=
  HomologicalComplex.Hom.isoOfComponents (fun r => biprodIso F (D.X r) (C.X (r - 1)))
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      obtain rfl : j = i - 1 := by omega
      simp only [Functor.mapHomologicalComplex_obj_d]
      change _ ≫ cone.d _ i (i - 1) = F.toFunctor.map (cone.d f i (i - 1)) ≫ _
      simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        Category.comp_id, biprodIso]
      apply biprod.hom_ext
      · simp [Preadditive.comp_add, ← Functor.map_comp]
      · simp [← Functor.map_comp])

/-- The pair map of the image is `κ ∘ F(ψ) ∘ ξ⁻¹`. -/
private lemma pairMap_map {C D : ChainComplex B ℤ} (f : C ⟶ D) {m n : ℤ} (hmn : m + 1 = n)
    (δφ : (StructureCx D).X n) (φ : (StructureCx C).X m)
    (hφ : (StructureCx C).d m (m - 1) φ = 0)
    (hδφ : (StructureCx D).d n m δφ = (StructureCx.push f).f m φ)
    (hφ' : (StructureCx (F.mapCx C)).d m (m - 1) (F.mapStructure C m φ) = 0)
    (hδφ' : (StructureCx (F.mapCx D)).d n m (F.mapStructure D n δφ) =
      (StructureCx.push ((F.toFunctor.mapHomologicalComplex _).map f)).f m
        (F.mapStructure C m φ)) :
    pairMap ((F.toFunctor.mapHomologicalComplex _).map f) hmn (F.mapStructure D n δφ)
        (F.mapStructure C m φ) hφ' hδφ' =
      (F.dualCxIso D n).hom ≫
        (F.toFunctor.mapHomologicalComplex _).map (pairMap f hmn δφ φ hφ hδφ) ≫
          (F.mapConeIso f).hom := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  change biprod.lift _ _ = (F.ξ (D.X (n - r))).inv ≫ F.toFunctor.map (biprod.lift _ _) ≫
    biprod.lift (F.toFunctor.map (biprod.fst : D.X r ⊞ C.X (r - 1) ⟶ _))
      (F.toFunctor.map (biprod.snd : D.X r ⊞ C.X (r - 1) ⟶ _))
  apply biprod.hom_ext
  · simp only [biprod.lift_fst, Category.assoc, ← Functor.map_comp]
    rfl
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← F.toFunctor.map_comp, biprod.lift_snd, map_units_smul'', Linear.comp_units_smul,
      F.toFunctor.map_comp,
      ← Category.assoc (F.ξ (D.X (n - r))).inv, inv_natural'', Category.assoc]
    rfl

end DualFunctor

namespace SymPair

/-- The image `(F f : F C ⟶ F D, F_% δφ, F_% φ)` of a strict `n`-dimensional Poincaré pair under a
duality functor `(F, ξ)`, with `(F_% φ)_r = F(φ_r) ∘ ξ⁻¹_{C_{n-1-r}}` and likewise for `δφ`. -/
@[simps]
noncomputable def map (F : DualFunctor B B') {m n : ℤ} (W : SymPair B m n) : SymPair B' m n where
  C := F.mapCx W.C
  D := F.mapCx W.D
  f := (F.toFunctor.mapHomologicalComplex _).map W.f
  δφ := F.mapStructure W.D n W.δφ
  φ := F.mapStructure W.C m W.φ
  dim := W.dim
  boundary_bounded := (W.boundary.map F).bounded
  boundary_cycle := (W.boundary.map F).cycle
  boundary_symmetric := (W.boundary.map F).symmetric
  boundary_poincare := (W.boundary.map F).poincare
  bounded r hr := F.toFunctor.map_isZero (W.bounded r hr)
  symmetric := by rw [F.mapStructure_T, W.symmetric]
  rel := by rw [F.mapStructure_d, W.rel, F.mapStructure_push]
  poincare := by
    obtain ⟨e, he⟩ := W.poincare
    refine ⟨(HomotopyEquiv.ofIso (F.dualCxIso W.D n)).trans
      ((F.toFunctor.mapHomotopyEquiv e).trans (HomotopyEquiv.ofIso (F.mapConeIso W.f))), ?_⟩
    refine Eq.trans ?_ (F.pairMap_map W.f W.dim W.δφ W.φ W.boundary_cycle W.rel _ _).symm
    rw [← he]
    rfl

end SymPair

end HSP
