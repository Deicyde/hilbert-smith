import Mathlib
import HilbertSmithPaper.Compression.CompressedPoincare
import HilbertSmithPaper.Compression.CompressedStandingData
import HilbertSmithPaper.Compression.BoundSequence
import HilbertSmithPaper.Corner.Actions.GraphTypeAction

/-!
# The compressed action

Take fixed local data with buffer radius `R` and nonempty control space `T`, and `0 < s < R / √n`.
Then `(Â_g, B̂_{g,h}, V̂_g)` with the bound sequence `(δ_i)` is a graph-type homotopy action of
`𝐆 = (ℤ/p^{max(i,1)}, χ_i)` on the compressed Poincaré complex `(C, φ̂)`, for the standing data of
the compression.

## Encoding

* The standing data is `standingData F hs hs'`; its `p`, `T`, `n`, `R`, `N` are those of `F`
  by definition, so the exterior quotient of the corner is `ℬ_{𝟏,Z}(T × Sⁿ)` of the compression.
* The Poincaré complex is asserted to exist together with the action, as in
  `compressed_poincare`: a strict Poincaré complex `P` on the compressed objects (`hX`), with
  chosen representatives `d`, `φ` of its differentials and structure (as `Corner.GraphAction`
  requires), whose level-`i` matrices are `d̂` and `φ̂`, and a graph-type action `Γ` with
  `Γ.δ = bound F` and `Γ.A`, `Γ.B`, `Γ.V` the compressed matrices `Â_g`, `B̂_{g,h}`, `V̂_g`.
* Matrices on `P.C.X r` are indexed by `Unit × Fin _`; the compressed matrices, on
  `Fin ((compressed F r).as.n i)`, are transported along `hX` by `Fin.cast`.
* The group element `g ∈ G_i = ℤ/p^{max(i,1)}` acts through `ZMod.cast g ∈ ℤ/p^i`, the index of
  the chain-model approximations (the identity for `i ≥ 1`; level `0` lies below `i₀ ≥ 1`, where
  every compressed matrix is empty).
* `compressed_action` (the declaration of the article); `N = n + 4`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Compression

open HSP.ChainModels FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The compressed action.** For nonempty `T` and `0 < s < R / √n`, `(Â_g, B̂_{g,h}, V̂_g)` with
the bound sequence `(δ_i)` is a graph-type homotopy action of `𝐆` on `(C, φ̂)`, for the standing
data of the compression. -/
theorem compressed_action (F : FixedLocalData p n D ρplus) [Nonempty F.T] {s : ℝ} (hs : 0 < s)
    (hs' : s < F.R / √n) :
    ∃ (P : SymPoincare (Ext (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)
        ((Set.univ : Set F.T) ×ˢ Corner.exterior n F.R)) ((n + 4 : ℕ) : ℤ))
      (hX : ∀ r, P.C.X r = (FiltQuot.functor _).obj (compressed F r))
      (d : ∀ a b : ℤ, (P.C.X a).as.as ⟶ (P.C.X b).as.as)
      (hd : ∀ a b, (FiltQuot.functor _).map (AsymCat.mkHom (d a b)) = P.C.d a b)
      (φ : ∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)},
        (P.C.X x.1.2).as.as ⟶ (P.C.X x.1.1).as.as)
      (hφ : ∀ x, (FiltQuot.functor _).map (AsymCat.mkHom (φ x)) = P.φ x)
      (Γ : Corner.GraphAction (standingData F hs hs') P d hd φ hφ),
      (∀ a b i, FreeCat.mat (AsymPre.coord (d a b) i) = fun y z =>
        compress F i a b (toMatrix ((chainModel F.toLocalDatum i).d a b))
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX b)) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX a)) z.2)) ∧
      (∀ x i, FreeCat.mat (AsymPre.coord (φ x) i) = fun y z =>
        phiHat F i x (Fin.cast (congrArg (fun M => M.as.as.n i) (hX x.1.1)) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX x.1.2)) z.2)) ∧
      Γ.δ = bound F ∧
      (∀ i g r, Γ.A i g r = fun y z =>
        AHat F i (ZMod.cast (g : ZMod (p ^ max i 1))) r
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX r)) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX r)) z.2)) ∧
      (∀ i g h r, Γ.B i g h r = fun y z =>
        BHat F i (ZMod.cast (g : ZMod (p ^ max i 1))) (ZMod.cast (h : ZMod (p ^ max i 1))) r
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX (r + 1))) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX r)) z.2)) ∧
      ∀ i g r, Γ.V i g r = fun y z =>
        VHat F i (ZMod.cast (g : ZMod (p ^ max i 1)))
          ⟨(r + 1, (n + 4 : ℕ) - r), by ring⟩
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX (r + 1))) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX ((n + 4 : ℕ) - r))) z.2) := by
  sorry

end HSP.Compression
