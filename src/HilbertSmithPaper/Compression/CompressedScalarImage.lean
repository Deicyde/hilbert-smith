import Mathlib
import HilbertSmithPaper.Compression.CompressedPoincare
import HilbertSmithPaper.Corner.Theorem.ScalarForget
import HilbertSmithPaper.Evaluation.Germ

/-!
# Scalar image of the compressed complex

For `Z_0` the exterior of `n` and the buffer radius `R`, `Z = T × Z_0`, and
`U' : ℬ_{𝟏,Z}(T × Sⁿ) → ℬ_{𝟏,Z_0}(Sⁿ)` forgetting to the scalar exterior quotient for the trivial
group sequence, `U'_* cls(C, φ̂) = 𝔪_{f_T}` in `𝕃_N(ℬ_{𝟏,Z_0}(Sⁿ))`, the germ of the torus test
map, with `(C, φ̂)` read in the idempotent completion through the Karoubi embedding.

## Encoding

* `(C, φ̂)` is any strict Poincaré complex `P` in `ℬ_{𝟏,Z}(T × Sⁿ)` on the compressed objects
  (`hX`) whose differentials and structure components are represented by `d̂` and `φ̂`, as in
  `compressed_poincare` (which asserts that one exists); these data determine `P` up to the
  transport `hX`.
* `cls(C, φ̂)` is `cls _ _ (LGroup.mk (P.map (karEmb _)))`, as in the definition of the germ, and
  `U'_*` is `ultL.map (Corner.scalarForget n R T (GroupSeq.trivial p))`.
* The germ takes a continuous map `c : 𝕋ⁿ → Sⁿ`; the statement is for any continuous `c` equal
  to the torus test map `f_T` of the pinch radius `ρ` (which is continuous).
* `scalar_image` (the declaration of the article); `N = n + 4`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Compression

open HSP.ChainModels FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Scalar image of the compressed complex.** `U'_* cls(C, φ̂) = 𝔪_{f_T}` in
`𝕃_N(ℬ_{𝟏,Z_0}(Sⁿ))`. -/
theorem scalar_image (F : FixedLocalData p n D ρplus)
    (P : SymPoincare (Ext (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)
      ((Set.univ : Set F.T) ×ˢ Corner.exterior n F.R)) ((n + 4 : ℕ) : ℤ))
    (hX : ∀ r, P.C.X r = (FiltQuot.functor _).obj (compressed F r))
    (hd : ∀ r s, ∃ f, IsCompressedRep F f
        (fun i => compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))) ∧
      eqToHom (hX r).symm ≫ P.C.d r s ≫ eqToHom (hX s) = (FiltQuot.functor _).map f)
    (hφ : ∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)}, ∃ f, IsCompressedRep F f
        (fun i => phiHat F i x) ∧
      eqToHom (hX x.1.2).symm ≫ P.φ x ≫ eqToHom (hX x.1.1) = (FiltQuot.functor _).map f)
    (c : C(Torus n, Corner.RoundSphere n))
    (hc : ∀ x, c x = (torusTestMap F.toLocalDatum F.ρ x : Corner.RoundSphere n)) :
    ultL.map (Corner.scalarForget n F.R F.T (GroupSeq.trivial p)) ((n + 4 : ℕ) : ℤ)
        (cls _ _ (LGroup.mk (P.map (karEmb _)))) =
      Evaluation.germ F.toLocalDatum F.R c := by
  sorry

end HSP.Compression
