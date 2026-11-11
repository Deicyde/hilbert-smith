import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.PointFiltration
import HilbertSmithPaper.Categories.Asymptotic.PointIdeal
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualityFunctor

/-!
# Point category

`𝒱_𝐆 = 𝒫_𝐆 ⧸ 𝒮_𝐆` is the quotient of the sequence category by the finite-support subcategory
(`HSP.VCat G`, the paper's quotient `HSP.FiltQuot` by `HSP.SCat G`), and
`q : 𝒫_𝐆 → 𝒱_𝐆` is the quotient functor, a strict duality functor (`HSP.VCat.q`). The subcategory
carries the point filtration `HSP.SCat.karoubiFiltration`. By the point ideal, the morphisms of
`𝒱_𝐆` are the sequences `(u_i)` modulo equality for all but finitely many `i`
(`HSP.VCat.map_eq_iff`).
-/

open CategoryTheory

namespace HSP

variable {p : ℕ}

/-- The point category `𝒱_𝐆 = 𝒫_𝐆 ⧸ 𝒮_𝐆`. -/
abbrev VCat (G : GroupSeq p) : Type := FiltQuot (SCat G)

namespace VCat

variable (G : GroupSeq p)

/-- The quotient functor `q : 𝒫_𝐆 → 𝒱_𝐆`, a duality functor with `ξ = id`. -/
def q : DualFunctor (PCat G) (VCat G) := FiltQuot.q (SCat G)

/-- The quotient functor is a strict duality functor. -/
private theorem q_isStrict : (q G).IsStrict := FiltQuot.q_isStrict (SCat G)

variable {G}

/-- The morphisms of `𝒱_𝐆` are the sequences `(u_i)` modulo equality for all but finitely many
`i`. -/
theorem map_eq_iff {M N : PCat G} (u v : M ⟶ N) :
    (FiltQuot.functor (SCat G)).map u = (FiltQuot.functor (SCat G)).map v ↔
      {i | PCat.homCoord u i ≠ PCat.homCoord v i}.Finite := by
  rw [FiltQuot.functor_map_eq_iff]
  refine (SCat.ideal_iff (u - v)).trans ?_
  simp only [PCat.homCoord_sub, ne_eq, sub_eq_zero]

end VCat

end HSP
