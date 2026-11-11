import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare

/-!
# Complexes in a full subcategory

Let `𝒫` be a full additive subcategory of a duality category `ℬ`, closed under duality. If every
chain object of a strict `k`-dimensional symmetric Poincaré complex `(C, φ)` in `ℬ` lies in `𝒫`,
then the same data form a strict `k`-dimensional symmetric Poincaré complex in `𝒫`, whose image
under the inclusion is `(C, φ)`.

The homotopy equivalence `φ_♮` lifts through the inclusion because the inclusion is fully
faithful: chain maps and homotopies lift componentwise.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

section Lift

variable {V : Type*} [Category V] [Preadditive V] {W : Type*} [Category W] [Preadditive W]
  (F : V ⥤ W) [F.Additive] [F.Full] [F.Faithful]

/-- Homotopies lift through a fully faithful additive functor. -/
private noncomputable def liftHomotopy {K L : ChainComplex V ℤ} {f g : K ⟶ L}
    (h : Homotopy ((F.mapHomologicalComplex _).map f) ((F.mapHomologicalComplex _).map g)) :
    Homotopy f g where
  hom i j := F.preimage (h.hom i j)
  zero i j w := F.map_injective (by rw [Functor.map_preimage, h.zero i j w, F.map_zero])
  comm i := F.map_injective (by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    simpa [Functor.map_add, Functor.map_comp] using H)

/-- Homotopy equivalences lift through a fully faithful additive functor. -/
private noncomputable def liftHomotopyEquiv {K L : ChainComplex V ℤ}
    (e : HomotopyEquiv ((F.mapHomologicalComplex _).obj K) ((F.mapHomologicalComplex _).obj L)) :
    HomotopyEquiv K L where
  hom := (F.mapHomologicalComplex _).preimage e.hom
  inv := (F.mapHomologicalComplex _).preimage e.inv
  homotopyHomInvId := liftHomotopy F ((Homotopy.ofEq (by simp)).trans
    (e.homotopyHomInvId.trans (Homotopy.ofEq (by simp))))
  homotopyInvHomId := liftHomotopy F ((Homotopy.ofEq (by simp)).trans
    (e.homotopyInvHomId.trans (Homotopy.ofEq (by simp))))

end Lift

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B] (P : ObjectProperty B) [IsDualAdditive P]

/-- A complex with all chain objects in `𝒫`, as a complex in `𝒫`. -/
private def cxToSub (C : ChainComplex B ℤ) (hC : ∀ r, P (C.X r)) :
    ChainComplex P.FullSubcategory ℤ where
  X r := ⟨C.X r, hC r⟩
  d i j := ObjectProperty.homMk (C.d i j)
  shape i j h := ObjectProperty.hom_ext _ (C.shape i j h)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (C.d_comp_d i j k)

/-- A structure on `C`, as a structure on the complex in `𝒫`. -/
private def strToSub {C : ChainComplex B ℤ} (hC : ∀ r, P (C.X r)) {k : ℤ}
    (φ : (StructureCx C).X k) : (StructureCx (cxToSub P C hC)).X k :=
  fun x => ObjectProperty.homMk (φ x)

private lemma mapStructure_strToSub {C : ChainComplex B ℤ} (hC : ∀ r, P (C.X r)) {k : ℤ}
    (φ : (StructureCx C).X k) :
    (DualSubcategory.incl P).mapStructure (cxToSub P C hC) k (strToSub P hC φ) = φ :=
  funext fun _ => Category.id_comp _

private lemma mapStructure_injective (C : ChainComplex P.FullSubcategory ℤ) (k : ℤ) :
    Function.Injective ((DualSubcategory.incl P).mapStructure C k) := fun a b h =>
  funext fun x => ObjectProperty.hom_ext _ (by
    have := congrFun h x
    change 𝟙 _ ≫ (a x).hom = 𝟙 _ ≫ (b x).hom at this
    simpa using this)

omit [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B] [IsDualAdditive P] in
private lemma isZero_sub {X : B} (hX : P X) (h : IsZero X) :
    IsZero (⟨X, hX⟩ : P.FullSubcategory) :=
  ⟨fun Y => ⟨⟨⟨ObjectProperty.homMk (h.to_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_src _ _)⟩⟩,
    fun Y => ⟨⟨⟨ObjectProperty.homMk (h.from_ Y.obj)⟩, fun _ =>
      ObjectProperty.hom_ext _ (h.eq_of_tgt _ _)⟩⟩⟩

private lemma toHom_congr {C : ChainComplex B ℤ} {k : ℤ} {φ φ' : (StructureCx C).X k}
    (h : φ = φ') (hφ : (StructureCx C).d k (k - 1) φ = 0)
    (hφ' : (StructureCx C).d k (k - 1) φ' = 0) :
    StructureCx.toHom φ hφ = StructureCx.toHom φ' hφ' := by
  subst h
  rfl

/-- **Complexes in a full subcategory.** A strict `k`-dimensional symmetric Poincaré complex in
`ℬ` with all chain objects in `𝒫`, as one in `𝒫`. -/
noncomputable def SymPoincare.toSub {k : ℤ} (x : SymPoincare B k) (hx : ∀ r, P (x.C.X r)) :
    SymPoincare P.FullSubcategory k where
  C := cxToSub P x.C hx
  φ := strToSub P hx x.φ
  bounded r hr := isZero_sub P (hx r) (x.bounded r hr)
  cycle := mapStructure_injective P _ _ (by
    rw [← DualFunctor.mapStructure_d, mapStructure_strToSub, map_zero]
    exact x.cycle)
  symmetric := mapStructure_injective P _ _ (by
    rw [← DualFunctor.mapStructure_T, mapStructure_strToSub]
    exact x.symmetric)
  poincare := by
    have hcyc : (StructureCx (cxToSub P x.C hx)).d k (k - 1) (strToSub P hx x.φ) = 0 :=
      mapStructure_injective P _ _ (by
        rw [← DualFunctor.mapStructure_d, mapStructure_strToSub, map_zero]
        exact x.cycle)
    obtain ⟨e, he⟩ := x.poincare
    let e' : HomotopyEquiv ((DualSubcategory.incl P).mapCx (dualCx (cxToSub P x.C hx) k))
        ((DualSubcategory.incl P).mapCx (cxToSub P x.C hx)) :=
      (HomotopyEquiv.ofIso ((DualSubcategory.incl P).dualCxIso (cxToSub P x.C hx) k).symm).trans e
    refine ⟨liftHomotopyEquiv P.ι e', ?_⟩
    refine (P.ι.mapHomologicalComplex _).map_injective ?_
    refine (Functor.map_preimage (P.ι.mapHomologicalComplex _) e'.hom).trans ?_
    have h1 := (DualSubcategory.incl P).toHom_mapStructure (cxToSub P x.C hx) k
      (strToSub P hx x.φ) hcyc (by rw [mapStructure_strToSub]; exact x.cycle)
    rw [toHom_congr (mapStructure_strToSub P hx x.φ) _ x.cycle] at h1
    change ((DualSubcategory.incl P).dualCxIso (cxToSub P x.C hx) k).inv ≫ e.hom = _
    rw [he]
    exact (Iso.inv_comp_eq _).2 h1

/-- The image of `x.toSub` under the inclusion is `x`. -/
lemma SymPoincare.toSub_map {k : ℤ} (x : SymPoincare B k) (hx : ∀ r, P (x.C.X r)) :
    (⟨(DualSubcategory.incl P).mapCx (x.toSub P hx).C,
        (DualSubcategory.incl P).mapStructure _ k (x.toSub P hx).φ⟩ :
      Σ C : ChainComplex B ℤ, (StructureCx C).X k) = ⟨x.C, x.φ⟩ := by
  change (⟨x.C, (DualSubcategory.incl P).mapStructure _ k (strToSub P hx x.φ)⟩ :
    Σ C : ChainComplex B ℤ, (StructureCx C).X k) = ⟨x.C, x.φ⟩
  rw [mapStructure_strToSub]

end HSP
