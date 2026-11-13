import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.StrictDualityFunctor
import HilbertSmithPaper.Categories.Cuts.CutBoundary
import HilbertSmithPaper.Categories.Cuts.ExteriorCutIdentification
import HilbertSmithPaper.Corner.CutFlag
import HilbertSmithPaper.Corner.Exterior
import HilbertSmithPaper.Corner.ExteriorClosed
import HilbertSmithPaper.Corner.ExteriorFirstCut
import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap
import HilbertSmithPaper.Evaluation.ScalarComponentProjection

/-!
# Scalar iterated cut

For `n ≥ 1`, `R > 0` and `0 < s < R/√n`, `N = n + 4`, the scalar iterated cut
`Δ_𝟏 = π_+ ∘ d_n ∘ q_* ∘ ⋯ ∘ q_* ∘ d_1 ∘ j_* : 𝕃_N(ℬ_{𝟏,Z₀}(Sⁿ)) → 𝕃_4(𝒱_𝟏)`
(`HSP.Corner.scalarIteratedCut`), where `d_m` is the cut boundary for `(A_m, B_m, Z⁰_m)` with
`Z⁰_1 = Z₀` and `Z⁰_m = ∅` for `m ≥ 2`.

## Encoding

The private recursion `iterCut` builds `d_{m+1} ∘ q_* ∘ ⋯ ∘ d_1 ∘ j_*`, landing in
`𝕃_{N-(m+1)}(𝒜_{Y_{m+1}})`; degrees and supports are transported along the equalities
`N - m - 1 = N - (m + 1)` and `Y_{(n-1)+1} = Y_n`. The union and intersection of each cut are
`Y_{m-1}` and `Y_m` by the cut flag; all sets are invariant because `C_p` acts trivially on `Sⁿ`.
-/

open CategoryTheory

namespace HSP.Corner

variable {p : ℕ} [Fact p.Prime]

/-- Transport along an equality of degrees. -/
private noncomputable def castDeg' {A : Type} [Category A] [Preadditive A] [Linear ℚ A]
    [Limits.HasFiniteBiproducts A] [DualCat A] {k k' : ℤ} (h : k = k') : ultL A k →+ ultL A k' :=
  h ▸ AddMonoidHom.id _

/-- Transport along an equality of supports. -/
private noncomputable def castSupp {n : ℕ} {Y Y' : Set (RoundSphere n)} (h : Y = Y') (k : ℤ) :
    ultL (supp (G := GroupSeq.trivial p) Y :
      ObjectProperty (AsymCat (GroupSeq.trivial p) (RoundSphere n))).FullSubcategory k →+
      ultL (supp (G := GroupSeq.trivial p) Y' :
        ObjectProperty (AsymCat (GroupSeq.trivial p) (RoundSphere n))).FullSubcategory k :=
  h ▸ AddMonoidHom.id _

variable {n : ℕ} {R s : ℝ} (hn : 1 ≤ n) (hR : 0 < R) (hs : 0 < s) (hs' : s < R / √n)

include hn hR hs hs' in
/-- The iteration: after `m + 1` cuts, `𝕃_N(ℬ_{𝟏,Z₀}(Sⁿ)) → 𝕃_{N-m-1}(𝒜_{Y_{m+1}})`. -/
private noncomputable def iterCut :
    ∀ m : ℕ, m + 1 ≤ n →
      (ultL (Ext (GroupSeq.trivial p) (RoundSphere n) (exterior n R)) ((n + 4 : ℕ) : ℤ) →+
        ultL (supp (G := GroupSeq.trivial p) (cutY n s (m + 1)) :
          ObjectProperty (AsymCat (GroupSeq.trivial p) (RoundSphere n))).FullSubcategory
          (((n + 4 : ℕ) : ℤ) - (m + 1)))
  | 0, _ =>
    (castDeg' (by push_cast; ring)).comp
      ((cutBoundary (A := cutA n s 1) (B := cutB n s 1) (Z := exterior n R) (S := Set.univ)
          (Y := cutY n s 1)
          ((cut_flag n hn s hs).1 1 le_rfl hn).2.2.1.symm
          ((cut_flag n hn s hs).1 1 le_rfl hn).2.2.2.symm
          ((cut_flag n hn s hs).1 1 le_rfl hn).1 ((cut_flag n hn s hs).1 1 le_rfl hn).2.1
          (exterior_closed n hn R hR p (RoundSphere n)).1
          (fun _ _ hx => hx) (fun _ _ hx => hx) (fun _ _ hx => hx)
          (Set.disjoint_iff_inter_eq_empty.2 (exterior_first_cut n hn R s hR hs hs').2)
          ((n + 4 : ℕ) : ℤ)).comp
        (ultL.map (exteriorCutIdent (G := GroupSeq.trivial p) (exterior n R)).1 _))
  | m + 1, hm =>
    (castDeg' (by push_cast; ring)).comp
      ((cutBoundary (A := cutA n s (m + 2)) (B := cutB n s (m + 2)) (Z := ∅) (S := cutY n s (m + 1))
          (Y := cutY n s (m + 2))
          ((cut_flag n hn s hs).1 (m + 2) (by omega) hm).2.2.1.symm
          ((cut_flag n hn s hs).1 (m + 2) (by omega) hm).2.2.2.symm
          ((cut_flag n hn s hs).1 (m + 2) (by omega) hm).1
          ((cut_flag n hn s hs).1 (m + 2) (by omega) hm).2.1
          isClosed_empty (fun _ _ hx => hx) (fun _ _ hx => hx) (fun _ _ hx => hx)
          (Set.empty_disjoint _) _).comp
        ((ultL.map (FiltQuot.q (suppIn (G := GroupSeq.trivial p) (cutY n s (m + 1)) ∅)) _).comp
          (iterCut m (by omega))))

variable (p n R s) in
include hn hR hs hs' in
/-- **The scalar iterated cut** `Δ_𝟏 = π_+ ∘ d_n ∘ q_* ∘ ⋯ ∘ q_* ∘ d_1 ∘ j_*`. -/
noncomputable def scalarIteratedCut :
    ultL (Ext (GroupSeq.trivial p) (RoundSphere n) (exterior n R)) ((n + 4 : ℕ) : ℤ) →+
      ultL (VCat (GroupSeq.trivial p)) 4 :=
  (Evaluation.scalarComponentProj p n hn s hs).comp
    ((castSupp (congrArg (cutY n s) (Nat.sub_add_cancel hn)) 4).comp
      ((castDeg' (by omega)).comp (iterCut hn hR hs hs' (n - 1) (by omega))))

end HSP.Corner
