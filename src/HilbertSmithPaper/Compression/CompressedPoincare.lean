import Mathlib
import HilbertSmithPaper.Compression.CompressedMaps
import HilbertSmithPaper.Compression.CompressedRep
import HilbertSmithPaper.Categories.Supports.ExteriorQuotient
import HilbertSmithPaper.Corner.Exterior
import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex

/-!
# The compressed complex is Poincaré

For the exterior `Z_0` of `n` and the buffer radius `R` and `Z = T × Z_0`, `(C, φ̂)` with
differential `d̂` is a strict `N`-dimensional symmetric Poincaré complex in the exterior quotient
`ℬ_{𝟏,Z}(T × Sⁿ)`, concentrated in `[0, N]`, whose chain objects are the compressed objects. A
homotopy inverse of `φ̂_♮` is `b̂`, with homotopies `Ĥ` and `Ĥ'`.

## Encoding

* `ℬ_{𝟏,Z}(T × Sⁿ)` is `Ext (GroupSeq.trivial p) (T × Sⁿ) Z` with `Z = Set.univ ×ˢ exterior n R`;
  its objects and morphisms are images under the quotient functor `FiltQuot.functor _` of those
  of `𝒜_𝟏(T × Sⁿ)`.
* As for the labelled chain model, the complex is asserted to exist: a strict Poincaré complex
  `P` (`SymPoincare`, strict and symmetric by construction) with `P.C.X r` the image of
  `compressed F r` (`hX`), and with each differential, each component of `φ`, each component of
  the inverse `e.inv` of `φ_♮ = e.hom` and each component of the two homotopies the image of a
  morphism represented (`IsCompressedRep`) by the corresponding compressed matrices: `d̂`
  (compressions of the components `d r s`), `φ̂`, `b̂`, `Ĥ`, `Ĥ'`, transported along `hX`.
  Concentration in `[0, N]` is `IsZero (P.C.X r)` for `r ∉ [0, N]`. `N = n + 4`.
* `compressed_poincare` (the declaration of the article) is this existence statement.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.Compression

open HSP.ChainModels FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The compressed complex is Poincaré.** `(C, φ̂)`, with differential `d̂`, is a strict
`N`-dimensional symmetric Poincaré complex in `ℬ_{𝟏,Z}(T × Sⁿ)`, concentrated in `[0, N]`, on the
compressed objects, and `b̂` is a homotopy inverse of `φ̂_♮` with homotopies `Ĥ` and `Ĥ'`. -/
theorem compressed_poincare (F : FixedLocalData p n D ρplus) :
    ∃ (P : SymPoincare (Ext (GroupSeq.trivial p) (F.T × Corner.RoundSphere n)
        ((Set.univ : Set F.T) ×ˢ Corner.exterior n F.R)) ((n + 4 : ℕ) : ℤ))
      (hX : ∀ r, P.C.X r = (FiltQuot.functor _).obj (compressed F r)),
      (∀ r s, ∃ f, IsCompressedRep F f
          (fun i => compress F i r s (toMatrix ((chainModel F.toLocalDatum i).d r s))) ∧
        eqToHom (hX r).symm ≫ P.C.d r s ≫ eqToHom (hX s) = (FiltQuot.functor _).map f) ∧
      (∀ x : {x : ℤ × ℤ // x.1 + x.2 = ((n + 4 : ℕ) : ℤ)}, ∃ f, IsCompressedRep F f
          (fun i => phiHat F i x) ∧
        eqToHom (hX x.1.2).symm ≫ P.φ x ≫ eqToHom (hX x.1.1) = (FiltQuot.functor _).map f) ∧
      (∀ r : ℤ, r < 0 ∨ ((n + 4 : ℕ) : ℤ) < r → IsZero (P.C.X r)) ∧
      ∃ e : HomotopyEquiv (dualCx P.C ((n + 4 : ℕ) : ℤ)) P.C,
        e.hom = StructureCx.toHom P.φ P.cycle ∧
        (∀ r : ℤ, ∃ f, IsCompressedRep F (s := (n + 4 : ℕ) - r) f (fun i => bHat F i r) ∧
          eqToHom (hX r).symm ≫ e.inv.f r ≫ eqToHom (hX ((n + 4 : ℕ) - r)) =
            (FiltQuot.functor _).map f) ∧
        (∀ r : ℤ, ∃ f, IsCompressedRep F f (fun i => HHat F i r) ∧
          eqToHom (hX r).symm ≫ e.homotopyInvHomId.hom r (r + 1) ≫ eqToHom (hX (r + 1)) =
            (FiltQuot.functor _).map f) ∧
        (∀ r : ℤ, ∃ f, IsCompressedRep F (r := (n + 4 : ℕ) - r) (s := (n + 4 : ℕ) - (r + 1)) f
            (fun i => H'Hat F i r) ∧
          eqToHom (hX ((n + 4 : ℕ) - r)).symm ≫ e.homotopyHomInvId.hom r (r + 1) ≫
              eqToHom (hX ((n + 4 : ℕ) - (r + 1))) =
            (FiltQuot.functor _).map f) := by
  sorry

end HSP.Compression
