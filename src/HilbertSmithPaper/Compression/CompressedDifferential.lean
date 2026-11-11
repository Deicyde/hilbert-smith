import Mathlib
import HilbertSmithPaper.Compression.CompressedMaps
import HilbertSmithPaper.Compression.CompressedRep
import HilbertSmithPaper.Compression.BoundSequence

/-!
# Compressed differential

For `i ≥ i₀`, `d̂ d̂ = 0` and `pr_i d = d̂ pr_i`; for every `i`, `d̂` has propagation at most `δ_i`
for the labels of the compressed complex in `T × Sⁿ`. So `(C, d̂)` is a chain complex in
`𝒜_𝟏(T × Sⁿ)`, and `C_r` is a zero object for `r ∉ [0, N]`.

## Encoding

* `d̂` is written as the compression `compress F i r s (d r s)` of the component `d r s` of the
  differential of `D_i`, for all `r s` (it is `0` unless `s = r - 1`); the two identities are
  stated for all components. The propagation bound is stated for `d̂ : C_{r+1} → C_r`, with the
  labels `(compressed F r).as.x i` of the compressed complex and the bound sequence `bound F`.
* The chain complex is asserted to exist: a complex `C` of `𝒜_𝟏(T × Sⁿ)` with `C_r = compressed F r`
  (`hX`) whose differentials are represented (`IsCompressedRep`) by `d̂`, transported along `hX`.
  It is unique, because a morphism is determined by a representative.
* `compressed_d` (the declaration of the article) is the conjunction; `N = n + 4`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Compression

open HSP.ChainModels FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Compressed differential.** For `i ≥ i₀`, `d̂ d̂ = 0` and `pr_i d = d̂ pr_i`; for every `i`,
`d̂` has propagation at most `δ_i`; so `(C, d̂)` is a chain complex in `𝒜_𝟏(T × Sⁿ)`, and `C_r` is a
zero object for `r ∉ [0, N]`. -/
theorem compressed_d (F : FixedLocalData p n D ρplus) :
    (∀ i, startIndex F ≤ i → ∀ r s t : ℤ,
      compress F i s t (toMatrix ((chainModel F.toLocalDatum i).d s t)) *
          compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) = 0 ∧
        retainedProj F i s * toMatrix ((chainModel F.toLocalDatum i).d r s) =
          compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)) *
            retainedProj F i r) ∧
    (∀ (i : ℕ) (r : ℤ),
      (prop ((compressed F (r + 1)).as.x i) ((compressed F r).as.x i)
        (compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r))) : ℝ) ≤
          bound F i) ∧
    ∃ (C : ChainComplex (AsymCat (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)) ℤ)
      (hX : ∀ r, C.X r = compressed F r),
      (∀ r s, IsCompressedRep F (eqToHom (hX r).symm ≫ C.d r s ≫ eqToHom (hX s))
        (fun i => compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s)))) ∧
      ∀ r : ℤ, r < 0 ∨ ((n + 4 : ℕ) : ℤ) < r → IsZero (C.X r) := by
  sorry

end HSP.Compression
