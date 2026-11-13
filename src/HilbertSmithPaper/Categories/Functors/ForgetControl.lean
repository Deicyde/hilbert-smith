import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctors.CompositeDualityFunctor
import HilbertSmithPaper.Categories.Functors.Pushforward
import HilbertSmithPaper.Categories.Functors.ForgetGroup

/-!
# Forgetting the control space

For a compact metric `C_p`-space `T` and a compact metric space `X` with the trivial `C_p`-action,
`T × X` carries the maximum metric (Mathlib's product metric) and the product action, which is
the action on the first factor. Forgetting the control space is the duality functor
`U_c = U ∘ pr_* : 𝒜_𝐆(T × X) → 𝒜_𝐆(X) → 𝒜_𝟏(X)`, the pushforward along `pr = Prod.snd` followed by
forgetting the group (`HSP.forgetControl`, the composite `DualFunctor.comp`). Its strictness is
the separate result `HSP.forgetControl_isStrict` (module `ForgetControlStrict`).

Lean encoding. The projection is equivariant for the product action whatever the action on `X`,
so the functor is defined for any `C_p`-action on `X`; the triviality of the action on `X`
(`htriv`) is used only to describe the objects: `(n_i, x_i)` goes to
`(|G_i| n_i, pr ∘ x_i ∘ pr_2 ∘ (e^{G_i}_{n_i})⁻¹)` (`HSP.forgetControl_obj`). Isometry of the
action on `T` is not needed.
-/

open CategoryTheory

namespace HSP

variable {p : ℕ} {G : GroupSeq p}
  (T : Type*) [MetricSpace T] [CompactSpace T] [AddAction (ZMod p) T]
  (X : Type*) [MetricSpace X] [CompactSpace X] [AddAction (ZMod p) X]

/-- Forgetting the control space, `U_c = U ∘ pr_* : 𝒜_𝐆(T × X) → 𝒜_𝟏(X)`. -/
noncomputable def forgetControl :
    DualFunctor (AsymCat G (T × X)) (AsymCat (GroupSeq.trivial p) X) :=
  (push (G := G) (f := (Prod.snd : T × X → X)) continuous_snd fun _ _ => rfl).comp forgetGroup

variable {T X}

/-- With the trivial action on `X`, `U_c (n_i, x_i) = (|G_i| n_i, pr ∘ x_i ∘ pr_2 ∘ e⁻¹)`. -/
private theorem forgetControl_obj (htriv : ∀ (c : ZMod p) (x : X), c +ᵥ x = x)
    (M : AsymPre G (T × X)) :
    (forgetControl (G := G) T X).toFunctor.obj ⟨M⟩ =
      ⟨⟨fun i => Fintype.card (G.G i) * M.n i,
        fun i j => (M.x i ((groupEnum (G.G i) (M.n i)).symm j).2).2⟩⟩ := by
  show (⟨⟨fun i => Fintype.card (G.G i) * M.n i, fun i j =>
      G.χ i ((groupEnum (G.G i) (M.n i)).symm j).1 +ᵥ
        (M.x i ((groupEnum (G.G i) (M.n i)).symm j).2).2⟩⟩ : AsymCat _ X) = _
  congr 1
  simp only [AsymPre.mk.injEq, true_and]
  exact heq_of_eq (funext fun _ => funext fun _ => htriv _ _)

end HSP
