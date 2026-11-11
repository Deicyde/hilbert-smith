import HilbertSmithPaper.Evaluation.BasedToFree
import HilbertSmithPaper.ChainModels.Grid.Cp2Cells
import HilbertSmithPaper.Categories.Asymptotic.PointSequenceCategory
import HilbertSmithPaper.Categories.Asymptotic.TrivialGroupSequence
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare

/-!
# The constant sequence of `CP²`

Let `𝟏` be the trivial group sequence. The constant functor `Free(ℚ[{1}]) → 𝒫_𝟏`,
`M ↦ (M, M, …)`, `u ↦ (u, u, …)`, is a strict duality functor with `ξ = id`. The *constant
sequence* `𝐏 = (P, φ_P)` is the image of the cells of `CP²` under the composite of based vector
spaces over the trivial group and the constant functor: the strict `4`-dimensional symmetric
Poincaré complex in `𝒫_𝟏` with every coordinate `(P, φ_P)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Evaluation

variable (p : ℕ)

/-- The underlying functor `M ↦ (M, M, …)`. -/
private def constFunctor : FreeCat Unit ⥤ PCat (GroupSeq.trivial p) where
  obj M := fun _ => M
  map f := fun _ => f

private instance : (constFunctor p).Additive where
  map_add := PCat.hom_ext fun _ => rfl

private instance : (constFunctor p).Linear ℚ where
  map_smul _ _ := PCat.hom_ext fun _ => rfl

/-- The constant functor `Free(ℚ[{1}]) → 𝒫_𝟏` as a duality functor with `ξ = id`. -/
private def constDual : DualFunctor (FreeCat Unit) (PCat (GroupSeq.trivial p)) where
  toFunctor := constFunctor p
  ξ _ := Iso.refl _
  ξ_natural f := by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact PCat.hom_ext fun _ => rfl
  ξ_dual M := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]; exact DualCat.dualHom_id _

/-- The constant functor is a strict duality functor. -/
private theorem constDual_isStrict : (constDual p).IsStrict :=
  fun _ => ⟨rfl, rfl⟩

/-- **The constant sequence** `𝐏 = (P, φ_P)` in `𝒫_𝟏`: the cells of `CP²` read in
`Free(ℚ[{1}])` and placed in every coordinate. -/
noncomputable def cp2Seq : SymPoincare (PCat (GroupSeq.trivial p)) 4 :=
  ChainModels.cp2Cells.map (basedToFree.comp (constDual p))

end HSP.Evaluation
