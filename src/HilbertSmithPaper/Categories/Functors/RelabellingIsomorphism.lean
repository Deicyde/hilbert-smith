import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality
import HilbertSmithPaper.Categories.Asymptotic.PropRelabel
import HilbertSmithPaper.Categories.Asymptotic.PropOne

/-!
# Relabelling isomorphism

Let `M = (n_i, x_i)` and `M' = (n_i, x'_i)` be objects with `max_k d(x_i(k), x'_i(k)) → 0`. The
identity matrices give an isomorphism `f : M → M'` with `f^* = f⁻¹`.

The labels of `(g, k)` in `M` and in `M'` are `d(x_i(k), x'_i(k))` apart because the action is
isometric; by relabelling the propagation, the identity matrices have propagation at most this
error, which tends to `0`. They are mutually inverse and self-transpose.

Lean encoding: `HSP.relabelIso hx : ⟨⟨n, x⟩⟩ ≅ ⟨⟨n, x'⟩⟩`, with the hypothesis
`hx : Tendsto (fun i => max_k nndist (x_i k) (x'_i k)) atTop (𝓝 0)` (an empty maximum is `0`),
and `HSP.relabelIso_dual : (relabelIso hx).hom^* = (relabelIso hx).inv`.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  [IsIsometricVAdd (ZMod p) X]

/-- The identity matrices from `(n_i, x_i)` to `(n_i, x'_i)`, with propagation tending to `0`. -/
private def relabelHom (n : ℕ → ℕ) (x x' : ∀ i, Fin (n i) → X)
    (hx : Tendsto (fun i => Finset.univ.sup fun k => nndist (x i k) (x' i k)) atTop (𝓝 0)) :
    (⟨n, x⟩ : AsymPre G X) ⟶ ⟨n, x'⟩ :=
  AsymPre.homMk (fun i => 𝟙 (⟨n i⟩ : FreeCat (G.G i))) (by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx
      (fun _ => zero_le) fun i => ?_
    refine (prop_relabel_le (AsymPre.label ⟨n, x⟩ i) (AsymPre.label ⟨n, x⟩ i)
      (AsymPre.label ⟨n, x⟩ i) (AsymPre.label ⟨n, x'⟩ i) (1 : Matrix _ _ ℚ)).trans ?_
    rw [prop_one, zero_add]
    simp only [nndist_self]
    rw [show (Finset.univ.sup fun _ : G.G i × Fin (n i) => (0 : ℝ≥0)) = 0 from
      le_antisymm (Finset.sup_le fun _ _ => le_rfl) zero_le, zero_add]
    refine Finset.sup_le fun b _ => ?_
    simp only [AsymPre.label, nndist_vadd]
    exact Finset.le_sup (f := fun k => nndist (x i k) (x' i k)) (Finset.mem_univ b.2))

/-- The relabelling isomorphism `f : (n_i, x_i) → (n_i, x'_i)` given by the identity matrices,
when `max_k d(x_i(k), x'_i(k)) → 0`. -/
def relabelIso {n : ℕ → ℕ} {x x' : ∀ i, Fin (n i) → X}
    (hx : Tendsto (fun i => Finset.univ.sup fun k => nndist (x i k) (x' i k)) atTop (𝓝 0)) :
    (⟨⟨n, x⟩⟩ : AsymCat G X) ≅ ⟨⟨n, x'⟩⟩ where
  hom := AsymCat.mkHom (relabelHom n x x' hx)
  inv := AsymCat.mkHom (relabelHom n x' x (by simpa only [nndist_comm] using hx))
  hom_inv_id := by
    rw [← Functor.map_comp]
    exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => Category.id_comp _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => Category.id_comp _)

/-- The relabelling isomorphism is unitary: `f^* = f⁻¹`. -/
theorem relabelIso_dual {n : ℕ → ℕ} {x x' : ∀ i, Fin (n i) → X}
    (hx : Tendsto (fun i => Finset.univ.sup fun k => nndist (x i k) (x' i k)) atTop (𝓝 0)) :
    DualCat.dualHom (relabelIso (G := G) hx).hom = (relabelIso hx).inv :=
  congrArg AsymCat.mkHom (AsymPre.hom_ext fun i => DualCat.dualHom_id (⟨n i⟩ : FreeCat (G.G i)))

end HSP
