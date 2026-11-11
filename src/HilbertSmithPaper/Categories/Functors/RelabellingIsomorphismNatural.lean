import Mathlib
import HilbertSmithPaper.Categories.Functors.RelabellingIsomorphism

/-!
# The relabelling isomorphism is natural

Let `M = (n_i, x_i)`, `M' = (n_i, x'_i)`, `N = (m_i, y_i)` and `N' = (m_i, y'_i)` with
`max_k d(x_i(k), x'_i(k)) → 0` and `max_k d(y_i(k), y'_i(k)) → 0`. If `u : M → N` and
`u' : M' → N'` have the same matrices, then `[u'] ∘ f_M = f_N ∘ [u]` for the relabelling
isomorphisms `f` (`HSP.relabelIso_natural`), because every component of `f` is an identity matrix.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

/-- The relabelling isomorphisms commute with morphisms given by the same matrices. -/
theorem relabelIso_natural {n m : ℕ → ℕ} {x x' : ∀ i, Fin (n i) → X} {y y' : ∀ i, Fin (m i) → X}
    (hx : Tendsto (fun i => Finset.univ.sup fun k => nndist (x i k) (x' i k)) atTop (𝓝 0))
    (hy : Tendsto (fun i => Finset.univ.sup fun k => nndist (y i k) (y' i k)) atTop (𝓝 0))
    (u : (⟨n, x⟩ : AsymPre G X) ⟶ ⟨m, y⟩) (u' : (⟨n, x'⟩ : AsymPre G X) ⟶ ⟨m, y'⟩)
    (h : ∀ i, AsymPre.coord u i = AsymPre.coord u' i) :
    AsymCat.mkHom u ≫ (relabelIso hy).hom = (relabelIso hx).hom ≫ AsymCat.mkHom u' := by
  obtain ⟨⟨v, hv, hv'⟩, -⟩ := relabelIso_spec (G := G) hy
  obtain ⟨⟨w, hw, hw'⟩, -⟩ := relabelIso_spec (G := G) hx
  rw [hv, hw, ← Functor.map_comp, ← Functor.map_comp]
  refine congrArg AsymCat.mkHom (AsymPre.hom_ext fun i => ?_)
  rw [AsymPre.coord_comp, AsymPre.coord_comp, hv' i, hw' i, h i]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end HSP
