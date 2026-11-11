import Mathlib
import HilbertSmithPaper.Categories.Functors.Pushforward
import HilbertSmithPaper.Categories.Supports.SupportSubcategory

/-!
# Pushforward preserves support

Let `f : X → X'` be equivariant and continuous, `X` compact, and `S ⊆ X`, `S' ⊆ X'` with
`f(S) ⊆ S'`. Then `f_*` carries `𝒜_S` into `𝒜_{S'}` (`HSP.push_supp`): `f` is uniformly
continuous, so for `ε > 0` there is `δ > 0` with `d(x, s) < δ ⇒ d(f x, f s) < ε`, and `f s ∈ S'`.

Lean encoding: the support condition is the thickening condition of `HSP.supp`; the statement
needs neither that `S` and `S'` are closed nor that they are invariant.
-/

open CategoryTheory Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p}
  {X : Type*} [MetricSpace X] [AddAction (ZMod p) X] [CompactSpace X]
  {X' : Type*} [MetricSpace X'] [AddAction (ZMod p) X']

/-- The pushforward `f_*` carries `𝒜_S` into `𝒜_{S'}` when `f(S) ⊆ S'`. -/
theorem push_supp {f : X → X'} (hf : Continuous f)
    (hfe : ∀ (c : ZMod p) (x : X), f (c +ᵥ x) = c +ᵥ f x) {S : Set X} {S' : Set X'}
    (hSS' : Set.MapsTo f S S') {P : AsymCat G X} (hP : supp S P) :
    supp S' ((push hf hfe).toFunctor.obj P) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ :=
    Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  filter_upwards [hP δ hδ] with i hi k
  obtain ⟨s, hs, hd⟩ := Metric.mem_thickening_iff.1 (hi k)
  exact Metric.mem_thickening_iff.2 ⟨f s, hSS' hs, hfδ hd⟩

end HSP
