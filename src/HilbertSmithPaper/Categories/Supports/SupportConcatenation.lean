import HilbertSmithPaper.Categories.Supports.SupportSubcategory

/-!
# Concatenation of supported objects

The concatenation (the chosen biproduct `AsymCat.binaryBicone`) of two `S`-supported objects is
`S`-supported.
-/

open CategoryTheory Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The concatenation of two `S`-supported objects is `S`-supported. -/
theorem supp_sum {S : Set X} {P Q : AsymCat G X} (hP : supp S P) (hQ : supp S Q) :
    supp S (AsymCat.binaryBicone P Q).pt := by
  intro ε hε
  filter_upwards [hP ε hε, hQ ε hε] with i h1 h2 k
  change Fin.append (P.as.x i) (Q.as.x i) k ∈ _
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · rw [Fin.append_left]; exact h1 k
  · rw [Fin.append_right]; exact h2 k


end HSP
