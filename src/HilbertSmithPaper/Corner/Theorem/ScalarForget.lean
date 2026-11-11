import Mathlib
import HilbertSmithPaper.Corner.ExteriorClosed
import HilbertSmithPaper.Corner.RoundSphere
import HilbertSmithPaper.Categories.Functors.ForgetControlSupport
import HilbertSmithPaper.Categories.Supports.ExteriorFunctor

/-!
# Forgetting to the scalar exterior quotient

Let `T` be a compact metric `C_p`-space, possibly empty, and `𝐆` a group sequence. With the
exterior `Z₀ ⊆ S^n` of the round sphere and `Z = T × Z₀` (`Set.univ ×ˢ exterior n R`),
forgetting the control space `U^𝐆_c : 𝒜_𝐆(T × S^n) → 𝒜_𝟏(S^n)` carries `𝒜_Z` into `𝒜_{Z₀}`
(`HSP.forgetControl_supp`, the action on `S^n` being trivial), so it induces the strict duality
functor on exterior quotients
`U^𝐆 : ℬ_{𝐆,Z}(T × S^n) → ℬ_{𝟏,Z₀}(S^n)`, `M ↦ U^𝐆_c M`, `[u] ↦ [U^𝐆_c u]`
(`HSP.Corner.scalarForget n R T 𝐆`), with `U^𝐆 ∘ q = q' ∘ U^𝐆_c`
(`HSP.Corner.scalarForget_comp_q`). `U' = scalarForget n R T (GroupSeq.trivial p)`, and `U` is
`scalarForget n R T D.groupSeq` for the standing data `D`.

Lean encoding: the construction is the induced functor `HSP.extFunctor` applied to
`HSP.forgetControl`. It needs neither `n ≥ 1`, `R > 0`, isometry of the action on `T`, nor the
closedness of `Z₀`, so these are not parameters.
-/

open CategoryTheory

namespace HSP.Corner

variable (n : ℕ) (R : ℝ) {p : ℕ} (T : Type*) [MetricSpace T] [CompactSpace T]
  [AddAction (ZMod p) T] (G : GroupSeq p)

/-- `U_c` carries `𝒜_{T × Z₀}` into `𝒜_{Z₀}`. -/
private theorem forgetControl_exterior (P : AsymCat G (T × RoundSphere n))
    (hP : supp ((Set.univ : Set T) ×ˢ exterior n R) P) :
    supp (exterior n R) ((forgetControl (G := G) T (RoundSphere n)).toFunctor.obj P) :=
  forgetControl_supp (fun _ _ => rfl) hP

/-- The induced functor with its two properties (strictness and `U^𝐆 ∘ q = q' ∘ U^𝐆_c`). -/
private noncomputable def scalarForgetAux :=
  extFunctor (forgetControl (G := G) T (RoundSphere n)) (forgetControl_isStrict T _)
    (forgetControl_exterior n R T G)

/-- **Forgetting to the scalar exterior quotient**,
`U^𝐆 : ℬ_{𝐆,T×Z₀}(T × S^n) → ℬ_{𝟏,Z₀}(S^n)`, `M ↦ U^𝐆_c M`, `[u] ↦ [U^𝐆_c u]`. -/
noncomputable def scalarForget :
    DualFunctor (Ext G (T × RoundSphere n) ((Set.univ : Set T) ×ˢ exterior n R))
      (Ext (GroupSeq.trivial p) (RoundSphere n) (exterior n R)) :=
  (scalarForgetAux n R T G).1

/-- `U^𝐆` is a strict duality functor. -/
theorem scalarForget_isStrict : (scalarForget n R T G).IsStrict :=
  (scalarForgetAux n R T G).2.1

/-- `U^𝐆 ∘ q = q' ∘ U^𝐆_c`. -/
theorem scalarForget_comp_q :
    FiltQuot.functor (supp ((Set.univ : Set T) ×ˢ exterior n R)) ⋙
        (scalarForget n R T G).toFunctor =
      (forgetControl (G := G) T (RoundSphere n)).toFunctor ⋙
        FiltQuot.functor (supp (exterior n R)) :=
  (scalarForgetAux n R T G).2.2

end HSP.Corner
