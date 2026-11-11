import Mathlib
import HilbertSmithPaper.Corner.Theorem.ScalarForget
import HilbertSmithPaper.Corner.Theorem.ScalarIteratedCut
import HilbertSmithPaper.Corner.Actions.GraphTypeAction
import HilbertSmithPaper.Signatures.Tail.TailSignature
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateCls

/-!
# Theorem A

Under the standing data, for a strict `N`-dimensional symmetric Poincaré complex `(C, φ)` in
`ℬ_{𝟏,Z}(T × Sⁿ)` with a graph-type homotopy action of `𝐆`, every representative `(σ_i)` of
`σ_tail(Δ_𝟏 U'_* cls(C, φ))` is eventually divisible by `p`.

## Encoding

* The complex is `C : SymPoincare (Ext 𝟏 (T × Sⁿ) (T × Z₀)) N`, with chosen representatives
  `d`, `φ` of its structure maps (`hd`, `hφ`) carrying the graph-type action `Γ`, as in
  `GraphAction`; "concentrated in `[0, N]`" is `hconc`, in the form Theorem C supplies.
* `cls(C, φ)` is `cls` of `LGroup.mk (C.map (karEmb _))`, the complex read in the idempotent
  completion through the Karoubi embedding; `U'` is `scalarForget` for the trivial group sequence
  and `Δ_𝟏` is `scalarIteratedCut` for the `n, R, s` of the standing data.
* "Every representative `(σ_i)`" is a sequence `σ` with `↑σ = σ_tail(…)` in
  `Germ cofinite ℤ = ℤ^ℕ/ℤ^(ℕ)`; the conclusion is `p ∣ σ i` for all large `i`.
-/

open CategoryTheory Filter

namespace HSP.Corner

/-- **Theorem A.** Every representative `(σ_i)` of `σ_tail(Δ_𝟏 U'_* cls(C, φ))` satisfies
`p ∣ σ_i` for all sufficiently large `i`. -/
theorem theoremA (S : StandingData)
    (C : SymPoincare (Ext (GroupSeq.trivial S.p) (S.T × RoundSphere S.n)
      ((Set.univ : Set S.T) ×ˢ exterior S.n S.R)) (S.N : ℤ))
    (hconc : ∀ r : ℤ, r < 0 ∨ (S.N : ℤ) < r → Limits.IsZero (C.C.X r))
    (d : ∀ a b : ℤ, (C.C.X a).as.as ⟶ (C.C.X b).as.as)
    (hd : ∀ a b, (FiltQuot.functor _).map (AsymCat.mkHom (d a b)) = C.C.d a b)
    (φ : ∀ x : {x : ℤ × ℤ // x.1 + x.2 = (S.N : ℤ)}, (C.C.X x.1.2).as.as ⟶ (C.C.X x.1.1).as.as)
    (hφ : ∀ x, (FiltQuot.functor _).map (AsymCat.mkHom (φ x)) = C.φ x)
    (Γ : GraphAction S C d hd φ hφ) (σ : ℕ → ℤ)
    (hσ : (σ : Germ (cofinite : Filter ℕ) ℤ) =
      tailSign (GroupSeq.trivial S.p)
        (scalarIteratedCut S.p S.n S.R S.s S.one_le_n S.R_pos S.s_pos S.s_lt
          (ultL.map (scalarForget S.n S.R S.T (GroupSeq.trivial S.p)) (S.N : ℤ)
            (cls _ _ (LGroup.mk (C.map (karEmb _))))))) :
    ∀ᶠ i in atTop, (S.p : ℤ) ∣ σ i := by
  sorry

end HSP.Corner
