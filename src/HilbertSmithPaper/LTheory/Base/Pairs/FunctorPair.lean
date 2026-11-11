import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorPairMap
import HilbertSmithPaper.LTheory.Base.Complexes.FunctorPush
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
  symmetric := by rw [F.mapStructure_compat.2.1, W.symmetric]
  rel := by rw [F.mapStructure_compat.1, W.rel, F.mapStructure_pushforward]
  poincare := by
    obtain ⟨e, he⟩ := W.poincare
    refine ⟨(HomotopyEquiv.ofIso (F.dualCxIso W.D n)).trans
      ((F.toFunctor.mapHomotopyEquiv e).trans (HomotopyEquiv.ofIso (F.mapConeIso W.f))), ?_⟩
    refine Eq.trans ?_ (F.pairMap_map W.f W.dim W.δφ W.φ W.boundary_cycle W.rel).symm
    rw [← he]
    rfl

end SymPair

end HSP
