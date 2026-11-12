import Mathlib
import HilbertSmithPaper.Categories.Functors.RelabellingIsomorphism

/-!
# The relabelling isomorphism is unitary

For the relabelling isomorphism `f : (n_i, x_i) → (n_i, x'_i)` (isometric action,
`max_k d(x_i(k), x'_i(k)) → 0`), `f^* = f⁻¹` (`HSP.relabelIso_dual`): both are given by identity
matrices, and identity matrices are self-transpose.
-/

open CategoryTheory Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

/-- The relabelling isomorphism is unitary: `f^* = f⁻¹`. -/
theorem relabelIso_dual {n : ℕ → ℕ} {x x' : ∀ i, Fin (n i) → X}
    (hx : Tendsto (fun i => Finset.univ.sup fun k => nndist (x i k) (x' i k)) atTop (𝓝 0)) :
    DualCat.dualHom (relabelIso (G := G) hx).hom = (relabelIso hx).inv := by
  obtain ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩ := relabelIso_spec (G := G) hx
  rw [hu, hv, AsymCat.dualHom_mkHom]
  refine congrArg AsymCat.mkHom (AsymPre.hom_ext fun i => ?_)
  rw [AsymPre.coord_transpose, hu' i, hv' i]
  exact DualCat.dualHom_id _

end HSP
