import HilbertSmithPaper.Evaluation.LabelledModel
import HilbertSmithPaper.Corner.Exterior
import HilbertSmithPaper.Categories.Supports.ExteriorQuotient
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiEmbedding
import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateCls
import HilbertSmithPaper.LTheory.Ultimate.Groups.InducedMap

/-!
# The labelled-model class

Let `N = n + 4` and let `Z_0 ⊆ Sⁿ` be the exterior for `n` and `R`, in the round sphere. For
continuous `c : 𝕋ⁿ → Sⁿ`, the *labelled-model class* (or *germ*) `𝔪_c ∈ 𝕃_N(ℬ_{𝟏,Z_0}(Sⁿ))` is
the image, under the map induced by the quotient functor `𝒜_𝟏(Sⁿ) → ℬ_{𝟏,Z_0}(Sⁿ)` of the
exterior quotient, of `cls [D_i, φ_i]` for the labelled model with labels `c`. The strict complex
`(D_i, φ_i)` in `𝒜_𝟏(Sⁿ)` is read in `Kar 𝒜_𝟏(Sⁿ)` through the Karoubi embedding `M ↦ (M, 1)`,
so that its class lies in `L^p_N(𝒜_𝟏(Sⁿ))`.

Lean: the chain models `D_i` are built from a local datum `A` (for a prime `p`), so the class
takes `A` as a parameter, and `𝟏` is the trivial group sequence for `p`. The strict complex is
the one asserted by `labelledModel_poincare`, whose differential and structure are the classes of
`d` and `φ_i`. The hypotheses `n ≥ 1` and `R > 0` are not needed to form the class and are
omitted.
-/

open CategoryTheory HSP.ChainModels

namespace HSP.Evaluation

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **The labelled-model class** `𝔪_c = q_* cls [D_i, φ_i] ∈ 𝕃_{n+4}(ℬ_{𝟏,Z_0}(Sⁿ))`, for the
labelled model with labels `c` and `Z_0` the exterior for `n` and `R`. -/
noncomputable def germ (A : LocalDatum p n D ρplus) (R : ℝ)
    (c : C(Torus n, Corner.RoundSphere n)) :
    ultL (Ext (GroupSeq.trivial p) (Corner.RoundSphere n) (Corner.exterior n R))
      ((n + 4 : ℕ) : ℤ) :=
  ultL.map (FiltQuot.q _) _
    (cls _ _ (LGroup.mk ((labelledModel_poincare A c).choose.map (karEmb _))))

end HSP.Evaluation
