import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Groups.HomotopyIsometryInvariance
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareSum
import HilbertSmithPaper.LTheory.Localization.Decorations.ComplexInSubcategory
import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush

/-!
# Sums in a full subcategory

Let `𝒫` be a full additive subcategory of a duality category `ℬ`, closed under duality, and let
`(Z, ζ)`, `(C, φ)`, `(C', φ')` be strict `k`-dimensional symmetric Poincaré complexes in `𝒫`. If an
isomorphism `Z ≅ C ⊕ C'` of their images in `ℬ` carries `ζ` to `φ ⊕ φ'`, then the class of
`(Z, ζ)` in `L(𝒫)` is the sum of the classes of `(C, φ)` and `(C', φ')`.

The isomorphism, followed by the canonical isomorphism `C ⊕ C' ≅ C ⊕_𝒫 C'` (the inclusion
preserves sums), lifts to `𝒫` because the inclusion is fully faithful; it carries the structures
as required, which is checked after the inclusion, and homotopy-isometry invariance applies with
`χ = 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B] (P : ObjectProperty B) [IsDualAdditive P]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

private lemma mapStructure_injective' (C : ChainComplex P.FullSubcategory ℤ) (k : ℤ) :
    Function.Injective ((DualSubcategory.incl P).mapStructure C k) := fun a b h =>
  funext fun x => ObjectProperty.hom_ext _ (by
    have := congrFun h x
    change 𝟙 _ ≫ (a x).hom = 𝟙 _ ≫ (b x).hom at this
    simpa using this)

omit [IsDualAdditive P] in
private lemma push_comp_apply {V : Type*} [Category V] [Preadditive V] [Linear ℚ V]
    [HasFiniteBiproducts V] [DualCat V] {C D E : ChainComplex V ℤ} (f : C ⟶ D) (g : D ⟶ E)
    (n : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

/-- **Sums in a full subcategory.** If an isomorphism of the images in `ℬ` carries `ζ` to
`φ ⊕ φ'`, then `[Z, ζ] = [C, φ] + [C', φ']` in `L(𝒫)`. -/
theorem SymPoincare.mk_eq_add_of_sumIso {k : ℤ} (z x y : SymPoincare P.FullSubcategory k)
    (u : (DualSubcategory.incl P).mapCx z.C ≅
      (DualSubcategory.incl P).mapCx x.C ⊞ (DualSubcategory.incl P).mapCx y.C)
    (hu : (StructureCx.push u.hom).f k ((DualSubcategory.incl P).mapStructure _ k z.φ) =
      StructureCx.sum ((DualSubcategory.incl P).mapStructure _ k x.φ)
        ((DualSubcategory.incl P).mapStructure _ k y.φ)) :
    LGroup.mk z = LGroup.mk x + LGroup.mk y := by
  rw [LGroup.mk_add]
  obtain ⟨w, hw⟩ := SymPoincare.exists_sum_iso x y
  have : (DualSubcategory.incl P).toFunctor.Full := inferInstanceAs P.ι.Full
  have : (DualSubcategory.incl P).toFunctor.Faithful := inferInstanceAs P.ι.Faithful
  let ι' := (DualSubcategory.incl P).toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)
  let e : ι'.obj x.C ⊞ ι'.obj y.C ≅ ι'.obj (x.C ⊞ y.C) := (ι'.mapBiprod x.C y.C).symm
  let v : z.C ≅ x.C ⊞ y.C := ι'.preimageIso (u ≪≫ e)
  refine LGroup.mk_eq_of_homotopyIsometry z _ (HomotopyEquiv.ofIso (v ≪≫ w)) 0 ?_
  rw [map_zero, eq_comm, sub_eq_zero, ← hw]
  change (StructureCx.push (v.hom ≫ w.hom)).f k _ = _
  rw [push_comp_apply]
  congr 1
  apply mapStructure_injective' P
  rw [DualFunctor.mapStructure_pushforward, StructureCx.sum, map_add,
    DualFunctor.mapStructure_pushforward, DualFunctor.mapStructure_pushforward]
  change (StructureCx.push (ι'.map v.hom)).f k ((DualSubcategory.incl P).mapStructure _ k z.φ) =
    (StructureCx.push (ι'.map (biprod.inl : x.C ⟶ _ ⊞ y.C))).f k
        ((DualSubcategory.incl P).mapStructure _ k x.φ) +
      (StructureCx.push (ι'.map (biprod.inr : y.C ⟶ x.C ⊞ _))).f k
        ((DualSubcategory.incl P).mapStructure _ k y.φ)
  have hv : ι'.map v.hom = u.hom ≫ e.hom := ι'.map_preimage _
  have h1 : (StructureCx.push (ι'.map v.hom)).f k ((DualSubcategory.incl P).mapStructure _ k z.φ) =
      (StructureCx.push e.hom).f k
        ((StructureCx.push u.hom).f k ((DualSubcategory.incl P).mapStructure _ k z.φ)) := by
    rw [← push_comp_apply, ← hv]
  rw [h1, hu, StructureCx.sum, map_add, ← push_comp_apply, ← push_comp_apply]
  simp only [e, Iso.symm_hom, Functor.mapBiprod_inv]
  erw [biprod.inl_desc, biprod.inr_desc]

end HSP
