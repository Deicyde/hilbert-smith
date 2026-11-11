import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality
import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory

/-!
# Support subcategory

For `S ⊆ X`, `𝒜_S` (`HSP.supp S`) is the full subcategory of `𝒜_𝐆(X)` on the objects
`⟨(n_i, x_i)⟩` such that for every `ε > 0`, eventually all `x_i(k)` lie in the open
`ε`-thickening `Metric.thickening ε S` (empty when `S = ∅`, unlike a formulation through
`Metric.infDist`). The paper uses it for closed invariant `S`; the definition needs neither.

`𝒜_S` contains the zero object (the empty sequence), the concatenation of two of its objects
(a biproduct), and is closed under `M^* = M`: it is a full additive subcategory closed under
duality (`HSP.isDualAdditive_supp`, an instance), so the quotient by it and the Karoubi
filtrations by it are defined.
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The *support subcategory* `𝒜_S`: the objects `(n_i, x_i)` of `𝒜_𝐆(X)` such that for every
`ε > 0`, eventually all `x_i(k)` lie in the open `ε`-thickening of `S`. -/
def supp (S : Set X) : ObjectProperty (AsymCat G X) :=
  fun P => ∀ ε > 0, ∀ᶠ i in atTop, ∀ k, P.as.x i k ∈ Metric.thickening ε S

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
