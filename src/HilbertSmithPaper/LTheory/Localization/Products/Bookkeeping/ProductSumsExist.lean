import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.TensorSigns
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.PairingAdditiveLeft
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.PairingAdditiveRight
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandZero

/-!
# The sums in a tensor product of complexes exist

For a duality pairing `(⊠, κ) : B × E → B''` and complexes `C`, `D` with finitely many nonzero
chain objects, the direct sums `⨁_{p+q=r} C_p ⊠ D_q` exist: only the summands in the finite
support are nonzero, and `B''` has finite biproducts. In Mathlib's terms, the total complex of the
bicomplex `C_p ⊠ D_q` exists (`HasMapBifunctor`).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A family with finitely many nonzero members has a coproduct. -/
private lemma hasCoproduct_of_finite {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {α : Type*} (f : α → C) (hf : {a | ¬ IsZero (f a)}.Finite) :
    HasCoproduct f := by
  classical
  let g : hf.toFinset → C := fun a => f a
  let c : Cofan f := Cofan.mk (∐ g) fun a =>
    if h : a ∈ hf.toFinset then Limits.Sigma.ι g ⟨a, h⟩ else 0
  have hz : ∀ a, a ∉ hf.toFinset → IsZero (f a) := fun a ha => by
    by_contra h
    exact ha (hf.mem_toFinset.2 h)
  refine ⟨⟨⟨c, Cofan.IsColimit.mk c
    (fun s => Limits.Sigma.desc (f := g) fun b => s.inj (b : α)) ?_ ?_⟩⟩⟩
  · intro s j
    by_cases h : j ∈ hf.toFinset
    · simp [c, h]
    · exact (hz j h).eq_of_src _ _
  · intro s m hm
    refine Limits.Sigma.hom_ext (f := g) _ _ fun b => ?_
    rw [Limits.Sigma.ι_comp_desc, ← hm b]
    simp [c, b.2]

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

namespace DualityPairing

variable (P : DualityPairing B E B'')

/-- **The sums in a tensor product of complexes exist.** The direct sums
`⨁_{p+q=r} C_p ⊠ D_q` exist when `C` and `D` have finitely many nonzero chain objects. -/
lemma hasMapBifunctor_of_finite {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    HomologicalComplex.HasMapBifunctor C D (Functor.curry.obj P.tensor)
      (ComplexShape.down ℤ) := by
  intro r
  refine hasCoproduct_of_finite _
    (((hC.prod hD).preimage Subtype.val_injective.injOn).subset ?_)
  rintro ⟨⟨p, q⟩, hpq⟩ hx
  by_contra h
  exact hx (cxProd.isZero_of_not_mem_supp P hC hD (r := r) hpq fun hm =>
    h ((cxProd.mem_supp hC hD).1 hm).1)

end DualityPairing

end HSP
