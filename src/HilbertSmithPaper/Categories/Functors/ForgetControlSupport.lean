import Mathlib
import HilbertSmithPaper.Categories.Functors.ForgetControl
import HilbertSmithPaper.Categories.Functors.PushSupport
import HilbertSmithPaper.Categories.Functors.ForgetGroupSupport

/-!
# Forgetting the control space preserves support

In the setting of forgetting the control space (trivial action on `X`, `htriv`), for `S ⊆ X`
the functor `U_c` carries `𝒜_{T × S}` into `𝒜_S ⊆ 𝒜_𝟏(X)` (`HSP.forgetControl_supp`):
`pr(T × S) ⊆ S`, so the pushforward along `pr` carries `𝒜_{T × S}` into `𝒜_S`, and `S` is
invariant for the trivial action, so forgetting the group keeps it in `𝒜_S`.

Lean encoding: `T × S` is `Set.univ ×ˢ S`. Closedness of `S` is not needed; the trivial action is
isometric, which is what forgetting the group uses.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p}
  {T : Type*} [MetricSpace T] [CompactSpace T] [AddAction (ZMod p) T]
  {X : Type*} [MetricSpace X] [CompactSpace X] [AddAction (ZMod p) X]

/-- `U_c` carries `𝒜_{T × S}` into `𝒜_S`. -/
theorem forgetControl_supp (htriv : ∀ (c : ZMod p) (x : X), c +ᵥ x = x) {S : Set X}
    {P : AsymCat G (T × X)} (hP : supp (Set.univ ×ˢ S) P) :
    supp S ((forgetControl (G := G) T X).toFunctor.obj P) := by
  have : IsIsometricVAdd (ZMod p) X :=
    ⟨fun c => by convert isometry_id with x; exact htriv c x⟩
  exact forget_supp (fun c x hx => (htriv c x).symm ▸ hx)
    (push_supp continuous_snd (fun _ _ => rfl) (fun _ hx => hx.2) hP)

end HSP
