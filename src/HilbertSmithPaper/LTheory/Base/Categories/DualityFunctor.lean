import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Duality functor

A duality functor `(F, ξ) : A → B` between duality categories is a ℚ-linear (additive) functor
`F` with a natural isomorphism `ξ M : F (M^*) ≅ (F M)^*` such that `(ξ M)^* = ξ (M^*)`. Since
`(F M)^{**} = F M` and `F (M^{**}) = F M` hold only propositionally, the last equation is stated
with the transport along these equalities. The functor is *strict* if every `ξ M` is an identity
(a transport along an equality of objects). Composition: `ξ^{GF}_M = ζ_{F M} ∘ G (ξ_M)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A *duality functor* `(F, ξ) : A → B`: a ℚ-linear functor `F` with a natural isomorphism
`ξ M : F (M^*) ≅ (F M)^*` such that `(ξ M)^* = ξ (M^*)` (up to the canonical transports). -/
structure DualFunctor (A : Type u₁) [Category.{v₁} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A]
    (B : Type u₂) [Category.{v₂} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] where
  /-- The underlying functor. -/
  toFunctor : A ⥤ B
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear ℚ]
  /-- The duality isomorphism `ξ M : F (M^*) ≅ (F M)^*`. -/
  ξ (M : A) : toFunctor.obj (dual M) ≅ dual (toFunctor.obj M)
  /-- Naturality of `ξ`. -/
  ξ_natural {M N : A} (f : M ⟶ N) :
    toFunctor.map (dualHom f) ≫ (ξ M).hom = (ξ N).hom ≫ dualHom (toFunctor.map f)
  /-- `(ξ M)^* = ξ (M^*)`, with the transports along `(F M)^{**} = F M = F (M^{**})`. -/
  ξ_dual (M : A) :
    dualHom (ξ M).hom = eqToHom ((dual_dual (toFunctor.obj M)).trans
      (congrArg toFunctor.obj (dual_dual M)).symm) ≫ (ξ (dual M)).hom

namespace DualFunctor

attribute [instance] additive linear

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]

/-- A duality functor is *strict* if `ξ = id`: every `ξ M` is the identity of
`F (M^*) = (F M)^*`. -/
def IsStrict (F : DualFunctor A B) : Prop :=
  ∀ M : A, ∃ h : F.toFunctor.obj (dual M) = dual (F.toFunctor.obj M), (F.ξ M).hom = eqToHom h

/-- The identity duality functor, with `ξ = id`. -/
@[simps]
def id (A : Type u₁) [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
    [DualCat A] : DualFunctor A A where
  toFunctor := 𝟭 A
  ξ M := Iso.refl _
  ξ_natural f := by simp
  ξ_dual M := by simp

/-- The composite `(G, ζ) ∘ (F, ξ)` of duality functors, with `ξ^{GF}_M = ζ_{F M} ∘ G (ξ_M)`. -/
@[simps]
def comp (F : DualFunctor A B) (G : DualFunctor B E) : DualFunctor A E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  ξ M := G.toFunctor.mapIso (F.ξ M) ≪≫ G.ξ (F.toFunctor.obj M)
  ξ_natural {M N} f := by
    have h1 := F.ξ_natural f
    have h2 := G.ξ_natural (F.toFunctor.map f)
    simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← G.toFunctor.map_comp, h1, G.toFunctor.map_comp, Category.assoc, h2,
      Category.assoc]
  ξ_dual M := by
    simp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, DualCat.dualHom_comp]
    rw [G.ξ_dual]
    have h := G.ξ_natural (F.ξ M).hom
    have hinv : dualHom (G.toFunctor.map (F.ξ M).hom) = (G.ξ (dual (F.toFunctor.obj M))).inv ≫
        G.toFunctor.map (dualHom (F.ξ M).hom) ≫ (G.ξ (F.toFunctor.obj (dual M))).hom := by
      rw [h, Iso.inv_hom_id_assoc]
    rw [hinv, F.ξ_dual, G.toFunctor.map_comp, eqToHom_map]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_trans_assoc]

end DualFunctor

end HSP
