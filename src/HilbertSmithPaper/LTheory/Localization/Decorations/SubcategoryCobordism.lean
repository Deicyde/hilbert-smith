import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism
import HilbertSmithPaper.LTheory.Base.Pairs.PairTransport
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareNeg
import HilbertSmithPaper.LTheory.Localization.Decorations.ComplexInSubcategory
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorPairMap
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorStructureSum
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.LiftHomotopyEquiv
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushId

/-!
# Cobordisms in a full subcategory

Let `𝒫` be a full additive subcategory of a duality category `ℬ`, closed under duality, and let
`x`, `y` be strict `k`-dimensional symmetric Poincaré complexes in `𝒫`. A strict pair in `ℬ` whose
codomain has all chain objects in `𝒫` and whose boundary is isomorphic, compatibly with the
structures, to the sum of the images of `x` and `-y` is a cobordism between `x` and `y` in `𝒫`.

Transporting the pair along the identification of its boundary with the image of the sum `z` of `x`
and `-y` in `𝒫` gives a pair with boundary the image of `z`. Its codomain and structure lift to `𝒫`,
and so does its pair map, since the inclusion carries mapping cones and pair maps to mapping cones and
pair maps and is fully faithful.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B] (P : ObjectProperty B) [IsDualAdditive P]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- A complex with all chain objects in `𝒫`, as a complex in `𝒫`. -/
private def cxSub (C : ChainComplex B ℤ) (hC : ∀ r, P (C.X r)) :
    ChainComplex P.FullSubcategory ℤ where
  X r := ⟨C.X r, hC r⟩
  d i j := ObjectProperty.homMk (C.d i j)
  shape i j h := ObjectProperty.hom_ext _ (C.shape i j h)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (C.d_comp_d i j k)

/-- A structure on `C`, as a structure on the complex in `𝒫`. -/
private def strSub {C : ChainComplex B ℤ} (hC : ∀ r, P (C.X r)) {k : ℤ}
    (φ : (StructureCx C).X k) : (StructureCx (cxSub P C hC)).X k :=
  fun x => ObjectProperty.homMk (φ x)

private lemma incl_strSub {C : ChainComplex B ℤ} (hC : ∀ r, P (C.X r)) {k : ℤ}
    (φ : (StructureCx C).X k) :
    (DualSubcategory.incl P).mapStructure (cxSub P C hC) k (strSub P hC φ) = φ :=
  funext fun _ => Category.id_comp _

private lemma mapStructure_inj (C : ChainComplex P.FullSubcategory ℤ) (k : ℤ) :
    Function.Injective ((DualSubcategory.incl P).mapStructure C k) := fun a b h =>
  funext fun x => ObjectProperty.hom_ext _ (by
    have := congrFun h x
    change 𝟙 _ ≫ (a x).hom = 𝟙 _ ≫ (b x).hom at this
    simpa using this)

/-- A chain map into a complex with all chain objects in `𝒫`, lifted to `𝒫`. -/
private def homSub {C : ChainComplex P.FullSubcategory ℤ} {D : ChainComplex B ℤ}
    (hD : ∀ r, P (D.X r)) (f : (DualSubcategory.incl P).mapCx C ⟶ D) : C ⟶ cxSub P D hD where
  f r := ObjectProperty.homMk (f.f r)
  comm' i j _ := ObjectProperty.hom_ext _ (f.comm i j)

omit [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B] [IsDualAdditive P] in
private lemma isZero_sub' {X : B} (hX : P X) (h : IsZero X) :
    IsZero (⟨X, hX⟩ : P.FullSubcategory) :=
  ⟨fun Y => ⟨⟨⟨ObjectProperty.homMk (h.to_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_src _ _)⟩⟩,
    fun Y => ⟨⟨⟨ObjectProperty.homMk (h.from_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_tgt _ _)⟩⟩⟩

private lemma iso_cancel {C : Type*} [Category C] {X Y Z T : C} (a : X ≅ Y) (c : Z ≅ T)
    (g : Y ⟶ Z) : a.inv ≫ ((a.hom ≫ g ≫ c.hom) ≫ c.inv) = g := by
  simp

private lemma lift_pair {m n : ℤ} (W : SymPair B m n) (z : SymPoincare P.FullSubcategory m)
    (hz : (⟨W.C, W.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X m) =
      ⟨(DualSubcategory.incl P).mapCx z.C, (DualSubcategory.incl P).mapStructure z.C m z.φ⟩)
    (hD : ∀ r, P (W.D.X r)) :
    ∃ W' : SymPair P.FullSubcategory m n,
      (⟨W'.C, W'.φ⟩ : Σ C : ChainComplex P.FullSubcategory ℤ, (StructureCx C).X m) =
        ⟨z.C, z.φ⟩ := by
  obtain ⟨C, D, f, δφ, φ, dim, bb, bc, bs, bp, bounded, symmetric, rel, poincare⟩ := W
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hz
  obtain rfl := eq_of_heq h
  let ι := DualSubcategory.incl P
  let D' := cxSub P D hD
  let δ' := strSub P hD δφ
  let f' : z.C ⟶ D' := homSub P hD f
  have hrel : (StructureCx D').d n m δ' = (StructureCx.push f').f m z.φ := by
    apply mapStructure_inj P
    rw [← ι.mapStructure_compat.1, incl_strSub, ι.mapStructure_pushforward]
    exact rel
  refine ⟨
    { C := z.C
      D := D'
      f := f'
      δφ := δ'
      φ := z.φ
      dim := dim
      boundary_bounded := z.bounded
      boundary_cycle := z.cycle
      boundary_symmetric := z.symmetric
      boundary_poincare := z.poincare
      bounded := fun r hr => isZero_sub' P (hD r) (bounded r hr)
      symmetric := mapStructure_inj P _ _ (by
        rw [← ι.mapStructure_compat.2.1, incl_strSub]
        exact symmetric)
      rel := hrel
      poincare := ?_ }, rfl⟩
  obtain ⟨e, he⟩ := poincare
  let e' : HomotopyEquiv (ι.mapCx (dualCx D' n)) (ι.mapCx (cone f')) :=
    (HomotopyEquiv.ofIso (ι.dualCxIso D' n).symm).trans
      (e.trans (HomotopyEquiv.ofIso (ι.mapConeIso f').symm))
  refine ⟨liftHomotopyEquiv P.ι e', ?_⟩
  apply (P.ι.mapHomologicalComplex _).map_injective
  refine (Functor.map_preimage (P.ι.mapHomologicalComplex _) e'.hom).trans ?_
  have hpm := ι.pairMap_map f' dim δ' z.φ z.cycle hrel
    ((ι.mapStructure_compat.1 _ _ _ _).trans (by rw [z.cycle, map_zero]))
    (by rw [ι.mapStructure_compat.1, hrel, ι.mapStructure_pushforward])
  have hpe : pairMap ((ι.toFunctor.mapHomologicalComplex _).map f') dim (ι.mapStructure D' n δ')
      (ι.mapStructure z.C m z.φ) ((ι.mapStructure_compat.1 _ _ _ _).trans
        (by rw [z.cycle, map_zero]))
      (by rw [ι.mapStructure_compat.1, hrel, ι.mapStructure_pushforward]) = e.hom := by
    rw [he]
    congr 1
    exact incl_strSub P hD δφ
  change (ι.dualCxIso D' n).inv ≫ e.hom ≫ (ι.mapConeIso f').inv = _
  rw [← hpe, hpm]
  exact iso_cancel _ _ _

omit [IsDualAdditive P] in
private lemma push_comp_apply' {C D E : ChainComplex B ℤ} (f : C ⟶ D) (g : D ⟶ E) (n : ℤ)
    (φ : (StructureCx C).X n) :
    (StructureCx.push (f ≫ g)).f n φ = (StructureCx.push g).f n ((StructureCx.push f).f n φ) := by
  rw [StructureCx.push_comp]
  rfl

private lemma iso_of_sigma_eq' {k : ℤ} {C₀ C : ChainComplex P.FullSubcategory ℤ}
    {φ₀ : (StructureCx C₀).X k} {φ : (StructureCx C).X k}
    (h : (⟨C₀, φ₀⟩ : Σ C : ChainComplex P.FullSubcategory ℤ, (StructureCx C).X k) = ⟨C, φ⟩) :
    ∃ u : C ≅ C₀, (StructureCx.push u.hom).f k φ = φ₀ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, StructureCx.push_id]; rfl⟩

/-- **Cobordisms in a full subcategory.** Strict symmetric Poincaré complexes `x`, `y` in `𝒫` are
cobordant in `𝒫` if a strict pair in `ℬ` whose codomain has all chain objects in `𝒫` has boundary
isomorphic to `(x ⊕ y, φ_x ⊕ (-φ_y))` in `ℬ`. -/
theorem SymPoincare.cobordant_of_pair {k : ℤ} (x y : SymPoincare P.FullSubcategory k)
    (W : SymPair B k (k + 1))
    (u : (DualSubcategory.incl P).mapCx x.C ⊞ (DualSubcategory.incl P).mapCx y.C ≅ W.C)
    (hu : (StructureCx.push u.hom).f k
      (StructureCx.sum ((DualSubcategory.incl P).mapStructure _ k x.φ)
        (-(DualSubcategory.incl P).mapStructure _ k y.φ)) = W.φ)
    (hD : ∀ r, P (W.D.X r)) : Cobordant x y := by
  let ι := DualSubcategory.incl P
  let ι' := ι.toFunctor.mapHomologicalComplex (ComplexShape.down ℤ)
  obtain ⟨z, hz₀⟩ := SymPoincare.exists_sum x y.neg
  have hz : (⟨z.C, z.φ⟩ : Σ C : ChainComplex P.FullSubcategory ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ (-y.φ)⟩ := hz₀
  obtain ⟨s, hs⟩ := iso_of_sigma_eq' P hz.symm
  let v : ι.mapCx z.C ≅ W.C := ι'.mapIso s ≪≫ ι'.mapBiprod x.C y.C ≪≫ u
  have hv : (StructureCx.push v.hom).f k (ι.mapStructure z.C k z.φ) = W.φ := by
    have h1 : (StructureCx.push (ι'.map s.hom)).f k (ι.mapStructure z.C k z.φ) =
        ι.mapStructure _ k (StructureCx.sum x.φ (-y.φ)) := by
      rw [← DualFunctor.mapStructure_pushforward, hs]
    have h2 : (StructureCx.push (ι'.mapBiprod x.C y.C).hom).f k
        (ι.mapStructure _ k (StructureCx.sum x.φ (-y.φ))) =
        StructureCx.sum (ι.mapStructure _ k x.φ) (ι.mapStructure _ k (-y.φ)) := by
      rw [← DualFunctor.mapStructure_sum, ← push_comp_apply', Iso.inv_hom_id, StructureCx.push_id]
      rfl
    change (StructureCx.push (ι'.map s.hom ≫ (ι'.mapBiprod x.C y.C).hom ≫ u.hom)).f k _ = _
    rw [push_comp_apply', h1, push_comp_apply', h2, map_neg, hu]
  obtain ⟨W₁, hW₁⟩ := SymPair.transport W v _ hv 1
  have hb : (⟨W₁.C, W₁.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨ι.mapCx z.C, ι.mapStructure z.C k z.φ⟩ := by
    have := congrArg (fun d : SymPair.Data B k (k + 1) =>
      (⟨d.1, d.2.2.2.2⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k)) hW₁
    simpa only [one_smul] using this
  have hD₁ : ∀ r, P (W₁.D.X r) := by
    have hd : W₁.D = W.D := congrArg (fun d : SymPair.Data B k (k + 1) => d.2.1) hW₁
    intro r
    rw [hd]
    exact hD r
  obtain ⟨W', hW'⟩ := lift_pair P W₁ z hb hD₁
  exact ⟨W', hW'.trans hz⟩

end HSP
