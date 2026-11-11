import Mathlib
import HilbertSmithPaper.LocalData.Chart.TestRegionInvariant

/-!
# The action on the test region

For a local datum, the action of `ℤ_p` on `Ω` restricts to an action on the invariant test region
`Z⁺`: `a` sends `z ∈ Z⁺` to `a +ᵥ z` computed in `Ω`.

## Encoding

`HSP.LocalDatum.instAddActionZplus` (the declaration of the article) is the instance;
`HSP.LocalDatum.coe_vadd_Zplus` is its unfolding lemma.
-/

namespace HSP

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The action of `ℤ_[p]` on `Ω` restricted to the invariant set `Z⁺`. -/
instance LocalDatum.instAddActionZplus (A : LocalDatum p n D ρplus) :
    AddAction ℤ_[p] A.Zplus where
  vadd a z := ⟨a +ᵥ (z : A.Ω), A.vadd_mem_Zplus_Uplus.1 a z z.2⟩
  zero_vadd z := Subtype.ext (zero_vadd ℤ_[p] (z : A.Ω))
  add_vadd a b z := Subtype.ext (add_vadd a b (z : A.Ω))

@[simp]
theorem LocalDatum.coe_vadd_Zplus (A : LocalDatum p n D ρplus) (a : ℤ_[p]) (z : A.Zplus) :
    ((a +ᵥ z : A.Zplus) : A.Ω) = a +ᵥ (z : A.Ω) :=
  rfl

end HSP
