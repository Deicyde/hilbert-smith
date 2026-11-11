import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.Structure.Concatenation

/-!
# The concatenation is a biproduct

For the concatenation bicone, `fst ≫ inl + snd ≫ inr = 𝟙` (`HSP.AsymCat.binaryBicone_total`), since
this holds for the coordinate inclusions and projections of `Free(ℚ[G_i])` at every level. Hence
the concatenation is a binary biproduct.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The concatenation bicone satisfies `fst ≫ inl + snd ≫ inr = 𝟙`. -/
theorem AsymCat.binaryBicone_total (P Q : AsymCat G X) :
    (AsymCat.binaryBicone P Q).fst ≫ (AsymCat.binaryBicone P Q).inl +
      (AsymCat.binaryBicone P Q).snd ≫ (AsymCat.binaryBicone P Q).inr =
        𝟙 (AsymCat.binaryBicone P Q).pt := by
  obtain ⟨a, ha, ha'⟩ := AsymCat.binaryBicone_fst P Q
  obtain ⟨b, hb, hb'⟩ := AsymCat.binaryBicone_snd P Q
  obtain ⟨c, hc, hc'⟩ := AsymCat.binaryBicone_inl P Q
  obtain ⟨d, hd, hd'⟩ := AsymCat.binaryBicone_inr P Q
  rw [ha, hb, hc, hd]
  have h : a ≫ c + b ≫ d = 𝟙 _ := AsymPre.hom_ext fun i => by
    rw [AsymPre.coord_add, AsymPre.coord_comp, AsymPre.coord_comp, ha' i, hb' i, hc' i, hd' i,
      AsymPre.coord_id]
    exact FreeCat.binaryBicone_total _ _
  have h2 := congrArg (Quotient.functor (asymRel G X)).map h
  rw [CategoryTheory.Functor.map_add, Functor.map_comp, Functor.map_comp,
    CategoryTheory.Functor.map_id] at h2
  exact h2

end HSP
