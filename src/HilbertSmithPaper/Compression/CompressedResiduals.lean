import Mathlib
import HilbertSmithPaper.Compression.CompressedMaps

/-!
# Residual identities

For `i ≥ i₀` and `g, h ∈ G_i`, the compressed maps satisfy the chain-model identities up to
residual words `p_2 α Q β ȷ_0` through the discarded cells, exactly.

## Encoding

* All maps are matrices on the cells of `D_i` (a cell of `(D_i^{N-*})_r` is a cell of
  `(D_i)_{N-r}`), as in `compress`; `pr`, `in`, `Q` are `retainedProj`, `retainedInc`,
  `discardProj`, and on cochains `in^* = pr`, `pr^* = in`, `Q^* = Qᵀ` in the degrees of the
  underlying cells. `N = n + 4`.
* `d̂` is written as the compression `compress F i s t (d s t)` of the component `d s t` of the
  differential of `D_i` (or of `D_i^{N-*} = dualCx (D_i) N`, whose differential carries the sign
  `(-1)^r`), so that every identity is stated without transport along `r + 1 - 1 = r`. For the
  same reason the identities involving a map of degree `+1` (`B`, `b`, `H`, `H'`) are stated on
  degree `r + 1`; together they cover every degree.
* `d̂ V̂_g + V̂_g d̂` and `d̂ φ̂ - φ̂ d̂` are the differential of the structure complex,
  `(∂f)_{p,q} = d f_{p+1,q} + (-1)^p f_{p,q+1} d^*`, on the compressed components, and the
  duality involution is `(Tf)_{p,q} = (-1)^{pq} (f_{q,p})^*` (`StructureCx.T`); the dual of a
  matrix is its transpose.
* `residuals` (the declaration of the article) is the conjunction of items (1)-(7).
-/

namespace HSP.Compression

open HSP.ChainModels FreeQ
open scoped Matrix

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Residual identities.** For `i ≥ i₀` and `g, h ∈ G_i`, exactly:
1. `d̂ Â_g - Â_g d̂ = pr a_g Q d in`;
2. `Â_g Â_h - Â_{g+h} - d̂ B̂_{g,h} - B̂_{g,h} d̂ = -pr a_g Q a_h in + pr B_{g,h} Q d in`;
3. `Â_g φ̂ - φ̂ Â_{-g}^* - d̂ V̂_g - V̂_g d̂ = -pr a_g Q φ pr^* + pr φ Q^* a_{-g}^* pr^*`;
4. `d̂ φ̂ = φ̂ d̂`, `φ̂` is fixed by the duality involution, and `Â_0 = 1`;
5. `d̂ b̂ - b̂ d̂ = -in^* d Q^* b in + in^* b Q d in`;
6. `φ̂ b̂ - 1 - d̂ Ĥ - Ĥ d̂ = pr H Q d in - pr φ Q^* b in`;
7. `b̂ φ̂ - 1 - d̂ Ĥ' - Ĥ' d̂ = in^* d Q^* H' pr^* - in^* b Q φ pr^*`. -/
theorem residuals (F : FixedLocalData p n D ρplus) {i : ℕ} (hi : startIndex F ≤ i)
    (g h : ZMod (p ^ i)) :
    -- (1)
    (∀ r : ℤ,
      compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r)) *
          AHat F i g (r + 1) -
        AHat F i g r *
          compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r)) =
      retainedProj F i r * toMatrix (groupApprox F.toLocalDatum i g r) * discardProj F i r *
        toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r) * retainedInc F i (r + 1)) ∧
    -- (2)
    (∀ r : ℤ,
      AHat F i g (r + 1) * AHat F i h (r + 1) - AHat F i (g + h) (r + 1) -
          compress F i (r + 1 + 1) (r + 1)
              (toMatrix ((chainModel F.toLocalDatum i).d (r + 1 + 1) (r + 1))) *
            BHat F i g h (r + 1) -
        BHat F i g h r *
          compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r)) =
      -(retainedProj F i (r + 1) * toMatrix (groupApprox F.toLocalDatum i g (r + 1)) *
          discardProj F i (r + 1) * toMatrix (groupApprox F.toLocalDatum i h (r + 1)) *
          retainedInc F i (r + 1)) +
        retainedProj F i (r + 1) *
          toMatrix (productHomotopy F.toLocalDatum F.ρ_pos F.ρ_lt i g h r) *
          discardProj F i r * toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r) *
          retainedInc F i (r + 1)) ∧
    -- (3)
    (∀ (a b : ℤ) (hab : a + b = ((n + 4 : ℕ) : ℤ))
        (h₁ : a + 1 + b = ((n + 4 : ℕ) : ℤ) + 1) (h₂ : a + (b + 1) = ((n + 4 : ℕ) : ℤ) + 1),
      AHat F i g a * phiHat F i ⟨(a, b), hab⟩ -
          phiHat F i ⟨(a, b), hab⟩ * (AHat F i (-g) b)ᵀ -
        (compress F i (a + 1) a (toMatrix ((chainModel F.toLocalDatum i).d (a + 1) a)) *
            VHat F i g ⟨(a + 1, b), h₁⟩ +
          a.negOnePow • (VHat F i g ⟨(a, b + 1), h₂⟩ *
            (compress F i (b + 1) b
              (toMatrix ((chainModel F.toLocalDatum i).d (b + 1) b)))ᵀ)) =
      -(retainedProj F i a * toMatrix (groupApprox F.toLocalDatum i g a) * discardProj F i a *
          toMatrix ((chainModelDuality F.toLocalDatum i).φ ⟨(a, b), hab⟩) *
          retainedInc F i b) +
        retainedProj F i a * toMatrix ((chainModelDuality F.toLocalDatum i).φ ⟨(a, b), hab⟩) *
          (discardProj F i b)ᵀ * (toMatrix (groupApprox F.toLocalDatum i (-g) b))ᵀ *
          retainedInc F i b) ∧
    -- (4)
    ((∀ (a b : ℤ) (h₁ : a + 1 + b = ((n + 4 : ℕ) : ℤ)) (h₂ : a + (b + 1) = ((n + 4 : ℕ) : ℤ)),
      compress F i (a + 1) a (toMatrix ((chainModel F.toLocalDatum i).d (a + 1) a)) *
          phiHat F i ⟨(a + 1, b), h₁⟩ +
        a.negOnePow • (phiHat F i ⟨(a, b + 1), h₂⟩ *
          (compress F i (b + 1) b (toMatrix ((chainModel F.toLocalDatum i).d (b + 1) b)))ᵀ) =
        0) ∧
      (∀ (a b : ℤ) (hab : a + b = ((n + 4 : ℕ) : ℤ)) (hba : b + a = ((n + 4 : ℕ) : ℤ)),
        (a * b).negOnePow • (phiHat F i ⟨(b, a), hba⟩)ᵀ =
          phiHat F i ⟨(a, b), hab⟩) ∧
      ∀ r : ℤ, AHat F i 0 r = 1) ∧
    -- (5)
    (∀ r : ℤ,
      compress F i ((n + 4 : ℕ) - (r + 1)) ((n + 4 : ℕ) - r)
            (toMatrix ((dualCx (chainModel F.toLocalDatum i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r)) *
          bHat F i (r + 1) -
        bHat F i r *
          compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r)) =
      -(retainedProj F i ((n + 4 : ℕ) - r) *
          toMatrix ((dualCx (chainModel F.toLocalDatum i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r) *
          (discardProj F i ((n + 4 : ℕ) - (r + 1)))ᵀ *
          toMatrix ((chainModelDuality F.toLocalDatum i).b (r + 1)) * retainedInc F i (r + 1)) +
        retainedProj F i ((n + 4 : ℕ) - r) * toMatrix ((chainModelDuality F.toLocalDatum i).b r) *
          discardProj F i r * toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r) *
          retainedInc F i (r + 1)) ∧
    -- (6)
    (∀ r : ℤ,
      phiHat F i ⟨(r + 1, (n + 4 : ℕ) - (r + 1)), add_sub_cancel _ _⟩ * bHat F i (r + 1) - 1 -
          compress F i (r + 1 + 1) (r + 1)
              (toMatrix ((chainModel F.toLocalDatum i).d (r + 1 + 1) (r + 1))) *
            HHat F i (r + 1) -
        HHat F i r *
          compress F i (r + 1) r (toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r)) =
      retainedProj F i (r + 1) * toMatrix (chainModelH F.toLocalDatum i r) * discardProj F i r *
          toMatrix ((chainModel F.toLocalDatum i).d (r + 1) r) * retainedInc F i (r + 1) -
        retainedProj F i (r + 1) *
          toMatrix ((chainModelDuality F.toLocalDatum i).φ
            ⟨(r + 1, (n + 4 : ℕ) - (r + 1)), add_sub_cancel _ _⟩) *
          (discardProj F i ((n + 4 : ℕ) - (r + 1)))ᵀ *
          toMatrix ((chainModelDuality F.toLocalDatum i).b (r + 1)) * retainedInc F i (r + 1)) ∧
    -- (7)
    (∀ r : ℤ,
      bHat F i (r + 1) * phiHat F i ⟨(r + 1, (n + 4 : ℕ) - (r + 1)), add_sub_cancel _ _⟩ - 1 -
          compress F i ((n + 4 : ℕ) - (r + 1 + 1)) ((n + 4 : ℕ) - (r + 1))
              (toMatrix ((dualCx (chainModel F.toLocalDatum i) ((n + 4 : ℕ) : ℤ)).d
                (r + 1 + 1) (r + 1))) *
            H'Hat F i (r + 1) -
        H'Hat F i r *
          compress F i ((n + 4 : ℕ) - (r + 1)) ((n + 4 : ℕ) - r)
            (toMatrix ((dualCx (chainModel F.toLocalDatum i) ((n + 4 : ℕ) : ℤ)).d (r + 1) r)) =
      retainedProj F i ((n + 4 : ℕ) - (r + 1)) *
          toMatrix ((dualCx (chainModel F.toLocalDatum i) ((n + 4 : ℕ) : ℤ)).d
            (r + 1 + 1) (r + 1)) *
          (discardProj F i ((n + 4 : ℕ) - (r + 1 + 1)))ᵀ *
          toMatrix (chainModelH' F.toLocalDatum i (r + 1)) *
          retainedInc F i ((n + 4 : ℕ) - (r + 1)) -
        retainedProj F i ((n + 4 : ℕ) - (r + 1)) *
          toMatrix ((chainModelDuality F.toLocalDatum i).b (r + 1)) * discardProj F i (r + 1) *
          toMatrix ((chainModelDuality F.toLocalDatum i).φ
            ⟨(r + 1, (n + 4 : ℕ) - (r + 1)), add_sub_cancel _ _⟩) *
          retainedInc F i ((n + 4 : ℕ) - (r + 1))) := by
  sorry

end HSP.Compression
