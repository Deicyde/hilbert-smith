import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionMap
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare

/-!
# Ultimate L-group

`𝕃_k(A)` is the colimit of the sequence of groups
`L^{⟨0⟩}_k(A) → L^{⟨-1⟩}_k(A) → L^{⟨-2⟩}_k(A) → ⋯` along the transition maps `t`.
`ι_j : L^{⟨-j⟩}_k(A) → 𝕃_k(A)` is the map from stage `j` and `cls := ι_0 : L^p_k(A) → 𝕃_k(A)`.
For a strict symmetric Poincaré complex `(C, φ)` in `A` itself, `cls (C, φ)` is the class of its
image under the Karoubi embedding.

Lean: the colimit is taken in `AddCommGrpCat` along `Functor.ofSequence`. `ι_0` has source
`L^{⟨0⟩}_k(A) = L^p_{k+0}(C_{ℤ^0} A)`, so `cls` precomposes it with the transport along `k = k + 0`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

universe v u

/-- Transport of `L`-groups along an equality of degrees. -/
noncomputable def LGroup.castIndex {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] {m m' : ℤ} (h : m = m') : LGroup B m ≃+ LGroup B m' := by
  subst h
  exact AddEquiv.refl _

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The sequence `L^{⟨0⟩}_k(A) → L^{⟨-1⟩}_k(A) → ⋯` of lower L-groups and transition maps. -/
noncomputable def lowerLSeq (k : ℤ) : ℕ ⥤ AddCommGrpCat.{max u v} :=
  Functor.ofSequence fun j => AddCommGrpCat.ofHom (transitionLower A j k)

/-- The ultimate L-group `𝕃_k(A)`, the colimit of the lower L-groups `L^{⟨-j⟩}_k(A)` along the
transition maps. -/
noncomputable def ultL (k : ℤ) : Type (max u v) :=
  AddCommGrpCat.carrier (colimit (lowerLSeq A k))

noncomputable instance (k : ℤ) : AddCommGroup (ultL A k) :=
  (colimit (lowerLSeq A k)).str

/-- The map `ι_j : L^{⟨-j⟩}_k(A) → 𝕃_k(A)` from stage `j` of the colimit. -/
noncomputable def ultL.of (k : ℤ) (j : ℕ) : lowerL A j k →+ ultL A k :=
  (colimit.ι (lowerLSeq A k) j).hom

/-- `cls = ι_0 : L^p_k(A) → 𝕃_k(A)`. -/
noncomputable def cls (k : ℤ) : Lp A k →+ ultL A k :=
  (ultL.of A k 0).comp
    (LGroup.castIndex (B := Karoubi A) (show k = k + ((0 : ℕ) : ℤ) by simp)).toAddMonoidHom

/-- `cls (C, φ)` for a strict symmetric Poincaré complex in `A`: the class of its image under the
Karoubi embedding. -/
noncomputable abbrev clsOf {k : ℤ} (x : SymPoincare A k) : ultL A k :=
  cls A k (LGroup.mk (x.map (karEmb A)))

end HSP
