import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Structure.ConcatenationBilimit
import HilbertSmithPaper.Categories.Asymptotic.Structure.EmptyObjectZero

/-!
# The asymptotic category has finite biproducts

`𝒜_𝐆(X)` has a zero object (the empty sequence, `HSP.AsymCat.hasZeroObject`), binary biproducts
(the concatenation, `HSP.AsymCat.hasBinaryBiproducts`), and hence finite biproducts
(`HSP.AsymCat.hasFiniteBiproducts`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The empty sequence is a zero object. -/
instance AsymCat.hasZeroObject : HasZeroObject (AsymCat G X) :=
  AsymCat.isZero_zero.hasZeroObject

/-- The concatenation is a binary biproduct. -/
instance AsymCat.hasBinaryBiproducts : HasBinaryBiproducts (AsymCat G X) :=
  ⟨fun P Q => hasBinaryBiproduct_of_total (AsymCat.binaryBicone P Q)
    (AsymCat.binaryBicone_total P Q)⟩

/-- **`𝒜_𝐆(X)` has finite biproducts.** -/
instance AsymCat.hasFiniteBiproducts : HasFiniteBiproducts (AsymCat G X) := by
  have := hasFiniteProducts_of_has_binary_and_terminal (C := AsymCat G X)
  exact HasFiniteBiproducts.of_hasFiniteProducts

end HSP
