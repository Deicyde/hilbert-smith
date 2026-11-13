import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.Categories.Asymptotic.TrivialGroupSequence
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModel
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel
import HilbertSmithPaper.ChainModels.Grid.Torus
import HilbertSmithPaper.Corner.RoundSphere
import HilbertSmithPaper.LocalData.Chart.LocalDatum
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.BasedCategory

/-!
# Labelled objects

For a continuous `c : 𝕋ⁿ → Sⁿ`, the labelled object `L_c(r)` of `𝒜_𝟏(Sⁿ)` has based module
`(D_i)_r` at level `i`, the basis cell `b` labelled `c(x_b)`.

## Encoding

* `labelledPre A c r` is the object before the quotient; `labelledObj A c r` is its class in
  `AsymCat (GroupSeq.trivial p) (RoundSphere n)`.
* `unitMat` reads a rational matrix as an equivariant matrix for the trivial group (the basis
  `Unit × Fin m`).
* `IsChainModelRep A c f m` says that the morphism `f` between labelled objects is the class of
  the sequence of matrices `m_i`: some representative has coordinates exactly `m_i`.
-/

open CategoryTheory

namespace HSP.Evaluation

open HSP.ChainModels HSP.FreeQ

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The labelled object in degree `r`: `(D_i)_r` at level `i`, the basis cell `b` labelled
`c(x_b) ∈ Sⁿ`. -/
noncomputable def labelledPre (A : LocalDatum p n D ρplus)
    (c : C(Torus n, Corner.RoundSphere n)) (r : ℤ) :
    AsymPre (GroupSeq.trivial p) (Corner.RoundSphere n) where
  n i := ((chainModel A i).X r).dim
  x i b := c (chainModelLabel A i r b)

/-- The labelled object in degree `r`, in `𝒜_𝟏(Sⁿ)`. -/
noncomputable abbrev labelledObj (A : LocalDatum p n D ρplus)
    (c : C(Torus n, Corner.RoundSphere n)) (r : ℤ) :
    AsymCat (GroupSeq.trivial p) (Corner.RoundSphere n) :=
  ⟨labelledPre A c r⟩

/-- A rational matrix as an equivariant matrix for the trivial group. -/
def unitMat {m k : ℕ} (u : Matrix (Fin m) (Fin k) ℚ) : Matrix (Unit × Fin m) (Unit × Fin k) ℚ :=
  fun a b => u a.2 b.2

/-- The morphism `f` of `𝒜_𝟏(Sⁿ)` between labelled objects is the class of the sequence of
matrices `m_i`. -/
def IsChainModelRep (A : LocalDatum p n D ρplus) (c : C(Torus n, Corner.RoundSphere n))
    {r s : ℤ} (f : labelledObj A c r ⟶ labelledObj A c s)
    (m : ∀ i, Matrix (Fin ((chainModel A i).X s).dim) (Fin ((chainModel A i).X r).dim) ℚ) :
    Prop :=
  ∃ u : labelledPre A c r ⟶ labelledPre A c s,
    (∀ i, FreeCat.mat (AsymPre.coord u i) = unitMat (m i)) ∧ f = AsymCat.mkHom u

end HSP.Evaluation
