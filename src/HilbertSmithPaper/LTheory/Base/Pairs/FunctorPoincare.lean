import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.FunctorStructureLaws
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex

/-!
# Duality functors carry Poincaré complexes

A duality functor `(F, ξ) : B → B'` sends a strict `k`-dimensional symmetric Poincaré complex
`(C, φ)` to `(F C, F_% φ)` with `(F_% φ)_{r,s} = F(φ_{r,s}) ∘ ξ⁻¹_{C_s}`. The proof
obligations are:

1. `F_%` (`DualFunctor.mapStructure`) commutes with `∂` and with `T`
   (`DualFunctor.mapStructure_compat`);
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

end DualFunctor

namespace SymPoincare

/-- The image `(F C, F_% φ)` of a strict `k`-dimensional symmetric Poincaré complex under a
duality functor `(F, ξ)`, with `(F_% φ)_r = F(φ_r) ∘ ξ⁻¹_{C_{k-r}}`. -/
@[simps]
noncomputable def map (F : DualFunctor B B') {k : ℤ} (x : SymPoincare B k) : SymPoincare B' k where
  C := F.mapCx x.C
  φ := F.mapStructure x.C k x.φ
  bounded r hr := F.toFunctor.map_isZero (x.bounded r hr)
  cycle := by rw [F.mapStructure_compat.1, x.cycle, map_zero]
  symmetric := by rw [F.mapStructure_compat.2.1, x.symmetric]
  poincare := by
    obtain ⟨e, he⟩ := x.poincare
    refine ⟨(HomotopyEquiv.ofIso (F.dualCxIso x.C k)).trans (F.toFunctor.mapHomotopyEquiv e), ?_⟩
    rw [F.mapStructure_compat.2.2 x.C k x.φ x.cycle, ← he]
    rfl

end SymPoincare

end HSP
