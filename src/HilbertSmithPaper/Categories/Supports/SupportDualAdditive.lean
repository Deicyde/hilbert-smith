import HilbertSmithPaper.Categories.Supports.SupportSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory

/-!
# The support subcategory is additive

`𝒜_S` contains the zero object (the empty sequence), the concatenation of two of its objects (a
biproduct, with the coordinate inclusions and projections), and is closed under `M^* = M`: it is a
full additive subcategory closed under duality (`HSP.isDualAdditive_supp`, an instance), so the
quotient by it and the Karoubi filtrations by it are defined.
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- `𝒜_S` is a full additive subcategory closed under duality. -/
instance isDualAdditive_supp (S : Set X) : IsDualAdditive (supp S : ObjectProperty (AsymCat G X))
    where
  exists_zero := ⟨⟨AsymPre.zero⟩, fun _ _ => Eventually.of_forall fun _ k => k.elim0,
    AsymCat.isZero_zero⟩
  exists_biprod {V W} hV hW := by
    refine ⟨AsymCat.binaryBicone V W,
      ⟨isBinaryBilimitOfTotal _ (AsymCat.binaryBicone_total V W)⟩, fun ε hε => ?_⟩
    filter_upwards [hV ε hε, hW ε hε] with i h1 h2 k
    change Fin.append (V.as.x i) (W.as.x i) k ∈ _
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact h1 k
    · rw [Fin.append_right]; exact h2 k
  dual_mem h := h

end HSP
