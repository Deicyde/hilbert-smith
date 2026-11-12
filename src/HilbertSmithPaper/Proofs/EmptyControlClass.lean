import Mathlib
import HilbertSmithPaper.Categories.Supports.ExteriorQuotient
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareZero
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Groups.HomotopyIsometryInvariance
import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateCls

/-!
# The class over an empty space vanishes

If the metric `C_p`-space `X` is empty, every Poincaré complex `(C, φ)` in the exterior quotient
`ℬ_{𝐆,Z}(X)` has `cls(C, φ) = 0` in `𝕃_k(ℬ_{𝐆,Z}(X))`, with `(C, φ)` read in the idempotent
completion through the Karoubi embedding.

## Encoding

`cls_eq_zero_of_isEmpty` (the declaration of the article) takes `[IsEmpty X]`. The proof: an object
of `𝒜_𝐆(X)` has labels `Fin n_i → X`, so `n_i = 0` at every level and the object is zero; zero
objects stay zero in the quotient and in the idempotent completion; and a Poincaré complex whose
chain objects are all zero is homotopy-isometric to the zero complex.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- Over an empty space every object of `𝒜_𝐆(X)` is zero. -/
private theorem isZero_asymCat [IsEmpty X] (M : AsymCat G X) : IsZero M := by
  have hn : ∀ i, M.as.n i = 0 := fun i =>
    Nat.eq_zero_of_not_pos fun h => IsEmpty.false (M.as.x i ⟨0, h⟩)
  have h : 𝟙 M.as = (0 : M.as ⟶ M.as) := AsymPre.hom_ext fun i => FreeCat.hom_ext <|
    funext fun a => absurd a.2.isLt (by simp [AsymPre.free, hn i])
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 M = (CategoryTheory.Quotient.functor (asymRel G X)).map (𝟙 M.as) :=
        ((CategoryTheory.Quotient.functor (asymRel G X)).map_id M.as).symm
    _ = (CategoryTheory.Quotient.functor (asymRel G X)).map 0 := by rw [h]
    _ = 0 := Functor.map_zero _ _ _

/-- A Poincaré complex whose chain objects are all zero has class `0`. -/
private theorem mk_eq_zero_of_isZero {B : Type*} [Category B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {k : ℤ} (x : SymPoincare B k)
    (hx : ∀ r, IsZero (x.C.X r)) : LGroup.mk x = 0 := by
  rw [LGroup.mk_zero]
  have hz : ∀ r, IsZero ((SymPoincare.zero (B := B) k).C.X r) := fun r => isZero_zero B
  exact LGroup.mk_eq_of_homotopyIsometry x _
    (HomotopyEquiv.ofIso (HomologicalComplex.Hom.isoOfComponents (fun r => (hx r).iso (hz r))
      (fun i _ _ => (hx i).eq_of_src _ _))) 0
    (funext fun y => (hz _).eq_of_tgt _ _)

/-- **The class over an empty space vanishes.** For an empty metric `C_p`-space `X`, every
Poincaré complex in `ℬ_{𝐆,Z}(X)` has `cls = 0`. -/
theorem cls_eq_zero_of_isEmpty [IsEmpty X] (Z : Set X) {k : ℤ} (P : SymPoincare (Ext G X Z) k) :
    cls _ k (LGroup.mk (P.map (karEmb _))) = 0 := by
  rw [mk_eq_zero_of_isZero _ fun r =>
    (karEmb _).toFunctor.map_isZero ((FiltQuot.functor _).map_isZero (isZero_asymCat (P.C.X r).as)),
    map_zero]

end HSP
