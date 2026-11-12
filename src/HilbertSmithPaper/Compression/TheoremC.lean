import Mathlib
import HilbertSmithPaper.Compression.CompressedAction
import HilbertSmithPaper.Compression.CompressedScalarImage
import HilbertSmithPaper.Compression.BoundSequence
import HilbertSmithPaper.Corner.Theorem.ScalarForget
import HilbertSmithPaper.Evaluation.Germ

/-!
# Theorem C

Take fixed local data with buffer radius `R`, torus test map `f_T` and control space `T`
(possibly empty), with the orbit metric and the cyclic action; `Z_0 ⊆ Sⁿ` is the exterior for `n`
and `R` and `Z = T × Z_0`; `G_i = ℤ/p^{max(i,1)}` with `χ_i` reduction mod `p`. For the compressed
complex `(C, φ̂)` with its compressed maps and the bound sequence `(δ_i)`:
1. `(C, φ̂)` is a strict `N`-dimensional symmetric Poincaré complex in `ℬ_{𝟏,Z}(T × Sⁿ)`,
   concentrated in `[0, N]`, on objects of `ℬ_{𝟏,Z}(T × Sⁿ)`;
2. if `T` is nonempty, then for every `0 < s < R/√n` these data form standing data, and
   `(Â, B̂, V̂, (δ_i))` is a graph-type homotopy action of `𝐆 = (G_i, χ_i)` on `(C, φ̂)`;
3. `U'_* cls(C, φ̂) = 𝔪_{f_T}` in `𝕃_N(ℬ_{𝟏,Z_0}(Sⁿ))`.

## Encoding

* As in `compressed_poincare` and `compressed_action`, the complex is asserted to exist: a strict
  Poincaré complex `P` (`SymPoincare`, strict and symmetric by construction) on the compressed
  objects (`hX`), with representatives `d`, `φ` of its differentials and structure (the
  parameters of `Corner.GraphAction`) whose level-`i` matrices are `d̂` and `φ̂`, transported along
  `hX` by `Fin.cast`. One `P` serves all three clauses. `N = n + 4`.
* (2): the standing data is `standingData F hs hs'` (`a_i = max i 1`, `χ_i` the reduction), whose
  construction carries the claim that these data form standing data; the action is a
  `Corner.GraphAction` with `δ = bound F` and matrices the compressed `Â_g`, `B̂_{g,h}`, `V̂_g`, the
  group element `g ∈ ℤ/p^{max(i,1)}` acting through `ZMod.cast g ∈ ℤ/p^i` (the identity for
  `i ≥ 1`; level `0` lies below the start index `i₀ ≥ 1`, where every compressed matrix is empty).
* (3): `cls(C, φ̂)` is `cls _ _ (LGroup.mk (P.map (karEmb _)))`, `U'_*` is
  `ultL.map (Corner.scalarForget n R T (GroupSeq.trivial p))`, and the germ is taken of any
  continuous `c` equal to `f_T` (the torus test map of the pinch radius `ρ`, which is continuous).
* `theoremC` (the declaration of the article).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Compression

open HSP.ChainModels FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Theorem C.** The compressed complex `(C, φ̂)` is a strict `N`-dimensional symmetric Poincaré
complex in `ℬ_{𝟏,Z}(T × Sⁿ)`, concentrated in `[0, N]`; for nonempty `T` and `0 < s < R/√n`,
`(Â, B̂, V̂, (δ_i))` is a graph-type homotopy action of `𝐆` on it for the standing data of the
compression; and `U'_* cls(C, φ̂) = 𝔪_{f_T}`. -/
theorem theoremC (F : FixedLocalData p n D ρplus) :
    ∃ (P : SymPoincare (Ext (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)
        ((Set.univ : Set F.T) ×ˢ Corner.exterior n F.R)) ((n + 4 : ℕ) : ℤ))
      (hX : ∀ r, P.C.X r = (FiltQuot.functor _).obj (compressed F r))
      (d : ∀ a b : ℤ, (P.C.X a).as.as ⟶ (P.C.X b).as.as)
      (hd : ∀ a b, (FiltQuot.functor _).map (AsymCat.mkHom (d a b)) = P.C.d a b)
      (φ : ∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)},
        (P.C.X x.1.2).as.as ⟶ (P.C.X x.1.1).as.as)
      (hφ : ∀ x, (FiltQuot.functor _).map (AsymCat.mkHom (φ x)) = P.φ x),
      (∀ a b i, FreeCat.mat (AsymPre.coord (d a b) i) = fun y z =>
        compress F i a b (toMatrix ((chainModel F.toLocalDatum i).d a b))
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX b)) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX a)) z.2)) ∧
      (∀ x i, FreeCat.mat (AsymPre.coord (φ x) i) = fun y z =>
        phiHat F i x (Fin.cast (congrArg (fun M => M.as.as.n i) (hX x.1.1)) y.2)
          (Fin.cast (congrArg (fun M => M.as.as.n i) (hX x.1.2)) z.2)) ∧
      -- (1) concentration in `[0, N]`
      (∀ r : ℤ, r < 0 ∨ ((n + 4 : ℕ) : ℤ) < r → IsZero (P.C.X r)) ∧
      -- (2)
      (∀ [Nonempty F.T] {s : ℝ} (hs : 0 < s) (hs' : s < F.R / √n),
        ∃ Γ : Corner.GraphAction (standingData F hs hs') P d hd φ hφ,
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
              (Fin.cast (congrArg (fun M => M.as.as.n i) (hX ((n + 4 : ℕ) - r))) z.2)) ∧
      -- (3)
      ∀ (c : C(Torus n, Corner.RoundSphere n)),
        (∀ x, c x = (torusTestMap F.toLocalDatum F.ρ x : Corner.RoundSphere n)) →
        ultL.map (Corner.scalarForget n F.R F.T (GroupSeq.trivial p)) ((n + 4 : ℕ) : ℤ)
            (cls _ _ (LGroup.mk (P.map (karEmb _)))) =
          Evaluation.germ F.toLocalDatum F.R c := by
  sorry

end HSP.Compression
