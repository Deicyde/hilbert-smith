import Mathlib
import HilbertSmithPaper.LTheory.Base.Complexes.Cone
import HilbertSmithPaper.LTheory.Base.Pairs.PairMap
import HilbertSmithPaper.LTheory.Localization.Boundary.UPair
import HilbertSmithPaper.LTheory.Localization.Decorations.ComplexInSubcategory
import HilbertSmithPaper.LTheory.Localization.Decorations.DecoratedObject

/-!
# Image of a pair with boundary in Kar U

For a strict `k`-dimensional `𝒰`-pair `V = (f : i P ⟶ D, δφ, i_% π)`, the *image*
`q V = (q D, q_% δφ)` is a strict `k`-dimensional symmetric Poincaré complex in `Dec(𝒜/𝒰)`.

`q ∘ i` sends every object to a zero object (the idempotent of `(V, e)`, `V ∈ 𝒰`, factors through
`V`), so `q f = 0`; hence `∂(q_% δφ) = q_%(f_% i_% π) = 0`, and the projection
`𝒞(q f) ⟶ q D` is an isomorphism carrying `q` of the pair map to `(q_% δφ)_♮`. The chain objects
`q D_r` are images, so decorated.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A] {U : ObjectProperty A} [IsDualAdditive U]

/-- `q ∘ i` sends every object of `Kar 𝒰` to a zero object. -/
private lemma isZero_q_i (X : Karoubi U.FullSubcategory) :
    IsZero ((FiltQuot.q U).kar.toFunctor.obj ((DualSubcategory.incl U).kar.toFunctor.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  refine Karoubi.hom_ext _ _ ?_
  change (FiltQuot.functor U).map X.p.hom = (FiltQuot.functor U).map 0
  rw [FiltQuot.functor_map_eq_iff]
  exact ⟨X.X.obj, X.X.property, X.p.hom, 𝟙 _, by simp⟩

/-- The projection `𝒞(q f) ⟶ q D`, an isomorphism when `q` kills the chain objects of `C`. -/
private noncomputable def coneIso {C D : ChainComplex (Karoubi A) ℤ} (f : C ⟶ D)
    (hC : ∀ r, IsZero ((FiltQuot.q U).kar.toFunctor.obj (C.X r))) :
    (FiltQuot.q U).kar.mapCx (cone f) ≅ (FiltQuot.q U).kar.mapCx D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r =>
      { hom := (FiltQuot.q U).kar.toFunctor.map biprod.fst
        inv := (FiltQuot.q U).kar.toFunctor.map biprod.inl
        hom_inv_id := by
          have h : (biprod.fst : D.X r ⊞ C.X (r - 1) ⟶ _) ≫ biprod.inl =
              𝟙 _ - biprod.snd ≫ biprod.inr := eq_sub_of_add_eq biprod.total
          rw [← Functor.map_comp, h, Functor.map_sub, Functor.map_comp,
            (hC (r - 1)).eq_of_tgt ((FiltQuot.q U).kar.toFunctor.map biprod.snd) 0, zero_comp,
            sub_zero]
          exact CategoryTheory.Functor.map_id _ _
        inv_hom_id := by
          rw [← Functor.map_comp, biprod.inl_fst]
          exact CategoryTheory.Functor.map_id _ _ })
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      change (FiltQuot.q U).kar.toFunctor.map biprod.fst ≫
          (FiltQuot.q U).kar.toFunctor.map (D.d i j) =
        (FiltQuot.q U).kar.toFunctor.map (cone.d f i j) ≫
          (FiltQuot.q U).kar.toFunctor.map biprod.fst
      rw [← Functor.map_comp, ← Functor.map_comp, cone.d, dite_eq_left (show i - 1 = j by omega),
        biprod.lift_fst, Functor.map_add, Units.smul_def, Functor.map_zsmul,
        Functor.map_comp (FiltQuot.q U).kar.toFunctor biprod.snd,
        (hC (i - 1)).eq_of_tgt ((FiltQuot.q U).kar.toFunctor.map biprod.snd) 0, zero_comp,
        smul_zero, add_zero])

namespace UPair

variable {k : ℤ} (V : UPair U k)

private lemma C_eq : V.V.C = (DualSubcategory.incl U).kar.mapCx V.P.C :=
  congrArg Sigma.fst V.boundary_eq

private lemma isZero_qC (r : ℤ) : IsZero ((FiltQuot.q U).kar.toFunctor.obj (V.V.C.X r)) := by
  rw [C_eq]
  exact isZero_q_i _

private lemma q_push_eq_zero :
    (FiltQuot.q U).kar.mapStructure V.V.D (k - 1)
      ((StructureCx.push V.V.f).f (k - 1) V.V.φ) = 0 := by
  funext ⟨⟨p, q⟩, h⟩
  rw [DualFunctor.mapStructure_apply, StructureCx.push_apply, Functor.map_comp, Functor.map_comp,
    (V.isZero_qC p).eq_of_src ((FiltQuot.q U).kar.toFunctor.map (V.V.f.f p)) 0, comp_zero,
    comp_zero, comp_zero]
  rfl

private lemma q_cycle :
    (StructureCx ((FiltQuot.q U).kar.mapCx V.V.D)).d k (k - 1)
      ((FiltQuot.q U).kar.mapStructure V.V.D k V.V.δφ) = 0 := by
  rw [DualFunctor.mapStructure_d, V.V.rel, q_push_eq_zero]

/-- `(q D, q_% δφ)` in `Kar(𝒜/𝒰)`. -/
private noncomputable def imageKar : SymPoincare (Karoubi (FiltQuot U)) k where
  C := (FiltQuot.q U).kar.mapCx V.V.D
  φ := (FiltQuot.q U).kar.mapStructure V.V.D k V.V.δφ
  bounded r hr := (FiltQuot.q U).kar.toFunctor.map_isZero (V.V.bounded r hr)
  cycle := V.q_cycle
  symmetric := by rw [DualFunctor.mapStructure_T, V.V.symmetric]
  poincare := by
    obtain ⟨e, he⟩ := V.V.poincare
    refine ⟨(HomotopyEquiv.ofIso ((FiltQuot.q U).kar.dualCxIso V.V.D k)).trans
      (((FiltQuot.q U).kar.toFunctor.mapHomotopyEquiv e).trans
        (HomotopyEquiv.ofIso (coneIso V.V.f V.isZero_qC))), ?_⟩
    refine HomologicalComplex.hom_ext _ _ fun r => ?_
    change ((FiltQuot.q U).kar.ξ (V.V.D.X (k - r))).inv ≫
      ((FiltQuot.q U).kar.toFunctor.map (e.hom.f r) ≫
        (FiltQuot.q U).kar.toFunctor.map (biprod.fst (X := V.V.D.X r) (Y := V.V.C.X (r - 1)))) = _
    rw [he, ← Functor.map_comp]
    simp only [pairMap, biprod.lift_fst]
    rfl

/-- **Image of a pair with boundary in Kar U.** `q V = (q D, q_% δφ)`, a strict `k`-dimensional
symmetric Poincaré complex in `Dec(𝒜/𝒰)`. -/
noncomputable def image : SymPoincare (Dec U) k :=
  SymPoincare.toSub (IsDecorated U) V.imageKar fun r => ⟨V.V.D.X r, rfl⟩

end UPair

end HSP
