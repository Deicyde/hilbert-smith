import HilbertSmithPaper.LTheory.Bounded.Categories.KZero

/-!
# Equality in `K_0`

`[P] = [Q]` in `K_0(Kar A)` iff `P ⊕ M ≅ Q ⊕ M` for some object `M` of `A` (viewed in `Kar A`
through `toKaroubi`). Grothendieck groups give `[P] = [Q]` iff `X ⊕ P ≅ X ⊕ Q` for some `X` in
`Kar A`; adding the complement of `X = (M, e)` gives `X ⊕ (M, 1 - e) ≅ M`
(Mathlib's `Karoubi.decomposition`).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

noncomputable section

namespace HSP

universe v u

namespace K0

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

private lemma of_eq_of_iff {M : Type*} [AddCommMonoid M] (x y : M) :
    Algebra.GrothendieckAddGroup.of x = Algebra.GrothendieckAddGroup.of y ↔
      ∃ c : M, c + x = c + y := by
  show (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).toAddMonoidHom x =
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).toAddMonoidHom y ↔ _
  rw [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply,
    AddSubmonoid.LocalizationMap.toAddMonoidHom_apply,
    ← AddLocalization.mk_zero_eq_addMonoidOf_mk, ← AddLocalization.mk_zero_eq_addMonoidOf_mk,
    AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by simpa using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, AddSubmonoid.mem_top c⟩, by simpa using hc⟩

/-- **Equality in `K_0`.** `[P] = [Q]` in `K_0(Kar A)` iff `P ⊕ M ≅ Q ⊕ M` for some object `M`
of `A`. -/
theorem cls_eq_iff (P Q : Karoubi A) :
    cls P = cls Q ↔ ∃ M : A, Nonempty (P ⊞ (toKaroubi A).obj M ≅ Q ⊞ (toKaroubi A).obj M) := by
  simp only [cls, of_eq_of_iff, ← IsoClasses.mk_eq_mk_iff, ← IsoClasses.mk_add]
  constructor
  · rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h X =>
      refine ⟨X.X, ?_⟩
      have hX : IsoClasses.mk ((toKaroubi A).obj X.X) =
          IsoClasses.mk X + IsoClasses.mk X.complement :=
        (IsoClasses.mk_eq_mk_iff.2 ⟨X.decomposition⟩).symm
      change IsoClasses.mk X + IsoClasses.mk P = IsoClasses.mk X + IsoClasses.mk Q at hc
      rw [hX, ← add_assoc, add_comm (IsoClasses.mk P), hc, add_comm _ (IsoClasses.mk Q),
        add_assoc]
  · rintro ⟨M, hM⟩
    exact ⟨IsoClasses.mk ((toKaroubi A).obj M), by rw [add_comm, hM, add_comm]⟩

end K0

end HSP

end
