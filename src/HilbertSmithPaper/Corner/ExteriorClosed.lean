import Mathlib
import HilbertSmithPaper.Corner.Exterior

/-!
# The exterior is closed

For `n ≥ 1`, `R > 0` and a compact metric space `T` with an isometric `C_p`-action, possibly empty,
the exterior `Z₀` is closed in `S^n`, and `Z = T × Z₀` is closed and `C_p`-invariant in `T × S^n`.

The proof uses neither `n ≥ 1`, `R > 0`, compactness of `T` nor isometry of the action: they are
the standing setting of the article and are kept (named with a leading underscore).
-/

namespace HSP.Corner

/-- The exterior `Z₀` is closed in `S^n`, and `Z = T × Z₀` is closed and `C_p`-invariant in
`T × S^n`. -/
theorem exterior_closed (n : ℕ) (_hn : 1 ≤ n) (R : ℝ) (_hR : 0 < R) (p : ℕ) (T : Type*)
    [MetricSpace T] [_hT : CompactSpace T] [AddAction (ZMod p) T]
    [_hiso : IsIsometricVAdd (ZMod p) T] :
    IsClosed (exterior n R) ∧ IsClosed ((Set.univ : Set T) ×ˢ exterior n R) ∧
      ∀ (c : ZMod p) (x : T × RoundSphere n),
        x ∈ (Set.univ : Set T) ×ˢ exterior n R → c +ᵥ x ∈ (Set.univ : Set T) ×ˢ exterior n R := by
  have h1 : IsClosed (exterior n R) := by
    have hc : (exterior n R)ᶜ =
        ((↑) : EuclideanSpace ℝ (Fin n) → RoundSphere n) '' Metric.ball 0 R := by
      ext x
      induction x using OnePoint.rec with
      | infty => simp [exterior]
      | coe z => simp [exterior]
    rw [← isOpen_compl_iff, hc]
    exact OnePoint.isOpen_image_coe.2 Metric.isOpen_ball
  exact ⟨h1, isClosed_univ.prod h1, fun _ _ hx => ⟨Set.mem_univ _, hx.2⟩⟩

end HSP.Corner
