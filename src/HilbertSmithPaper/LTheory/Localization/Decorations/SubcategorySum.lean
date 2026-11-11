import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Groups.HomotopyIsometryInvariance
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareSum
import HilbertSmithPaper.LTheory.Localization.Decorations.ComplexInSubcategory
import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush

/-!
# Sums in a full subcategory

Let `𝒫` be a full additive subcategory of a duality category `ℬ`, closed under duality, and let
`(Z, ζ)`, `(C, φ)`, `(C', φ')` be strict `k`-dimensional symmetric Poincaré complexes in `ℬ` with
all chain objects in `𝒫`. If an isomorphism `Z ≅ C ⊕ C'` carries `ζ` to `φ ⊕ φ'`, then the class
of `(Z, ζ)` in `L(𝒫)` is the sum of the classes of `(C, φ)` and `(C', φ')`.

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

private lemma mapStructure_strToSub' {k : ℤ} (x : SymPoincare B k)
    (hx : ∀ r, P (x.C.X r)) :
    (DualSubcategory.incl P).mapStructure _ k (x.toSub P hx).φ = x.φ :=
  funext fun _ => Category.id_comp _

omit [IsDualAdditive P] in
private lemma push_comp_apply {V : Type*} [Category V] [Preadditive V] [Linear ℚ V]
    [HasFiniteBiproducts V] [DualCat V] {C D E : ChainComplex V ℤ} (f : C ⟶ D) (g : D ⟶ E)
    (n : ℤ) (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

/-- **Sums in a full subcategory.** If an isomorphism `Z ≅ C ⊕ C'` carries `ζ` to `φ ⊕ φ'`,
then `[Z, ζ] = [C, φ] + [C', φ']` in `L(𝒫)`. -/
theorem SymPoincare.mk_toSub_of_sumIso {k : ℤ} (z x y : SymPoincare B k)
    (hz : ∀ r, P (z.C.X r)) (hx : ∀ r, P (x.C.X r)) (hy : ∀ r, P (y.C.X r))
    (u : z.C ≅ x.C ⊞ y.C) (hu : (StructureCx.push u.hom).f k z.φ = StructureCx.sum x.φ y.φ) :
    LGroup.mk (z.toSub P hz) = LGroup.mk (x.toSub P hx) + LGroup.mk (y.toSub P hy) := by
  rw [LGroup.mk_add]
  obtain ⟨w, hw⟩ := SymPoincare.exists_sum_iso (x.toSub P hx) (y.toSub P hy)
  let ι' := P.ι.mapHomologicalComplex (ComplexShape.down ℤ)
  let e : x.C ⊞ y.C ≅ ι'.obj ((x.toSub P hx).C ⊞ (y.toSub P hy).C) :=
    (ι'.mapBiprod (x.toSub P hx).C (y.toSub P hy).C).symm
  let v : (z.toSub P hz).C ≅ (x.toSub P hx).C ⊞ (y.toSub P hy).C := ι'.preimageIso (u ≪≫ e)
  refine LGroup.mk_eq_of_homotopyIsometry (z.toSub P hz) _ (HomotopyEquiv.ofIso (v ≪≫ w)) 0 ?_
  rw [map_zero, eq_comm, sub_eq_zero, ← hw]
  change (StructureCx.push (v.hom ≫ w.hom)).f k _ = _
  rw [push_comp_apply]
  congr 1
  apply mapStructure_injective' P
  rw [DualFunctor.mapStructure_pushforward, StructureCx.sum, map_add,
    DualFunctor.mapStructure_pushforward, DualFunctor.mapStructure_pushforward,
    mapStructure_strToSub', mapStructure_strToSub', mapStructure_strToSub']
  change (StructureCx.push (ι'.map v.hom)).f k z.φ =
    (StructureCx.push (ι'.map (biprod.inl : (x.toSub P hx).C ⟶ _ ⊞ (y.toSub P hy).C))).f k x.φ +
      (StructureCx.push (ι'.map (biprod.inr : (y.toSub P hy).C ⟶ (x.toSub P hx).C ⊞ _))).f k y.φ
  have hv : ι'.map v.hom = u.hom ≫ e.hom := ι'.map_preimage _
  have h1 : (StructureCx.push (ι'.map v.hom)).f k z.φ =
      (StructureCx.push e.hom).f k ((StructureCx.push u.hom).f k z.φ) := by
    rw [← push_comp_apply, ← hv]
    rfl
  rw [h1, hu, StructureCx.sum, map_add, ← push_comp_apply, ← push_comp_apply]
  simp only [e, Iso.symm_hom, Functor.mapBiprod_inv]
  erw [biprod.inl_desc, biprod.inr_desc]
  rfl

end HSP
