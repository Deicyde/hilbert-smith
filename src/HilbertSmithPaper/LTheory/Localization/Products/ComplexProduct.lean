import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing
import HilbertSmithPaper.LTheory.Localization.Products.BasedTensor

/-!
# Tensor product of complexes

For a duality pairing `(⊠, κ) : B × E → B''` and chain complexes `C` in `B`, `D` in `E`
(`ChainComplex _ ℤ`, differentials of degree `-1`), each with only finitely many chain objects that
are not zero objects, the tensor product `C ⊗ D` is the complex in `B''` with
`(C ⊗ D)_r = ⨁_{p+q=r} C_p ⊠ D_q` and differential `d ⊠ 1 + (-1)^p 1 ⊠ d` on `C_p ⊠ D_q`.

It is Mathlib's `HomologicalComplex.mapBifunctor` for the curried functor `⊠` and the complex
shape `ComplexShape.down ℤ`, whose total-complex signs are `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`
(the instance `TensorSigns (ComplexShape.down ℤ)` below, `ε p = (-1)^p`). The direct sum over
`p + q = r` is a coproduct of a family with finitely many nonzero members, which exists because
the categories have finite biproducts. For chain maps `f`, `g`, the chain map `f ⊗ g` is
`f_p ⊠ g_q` on `C_p ⊠ D_q` (`mapBifunctorMap`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The signs `ε p = (-1)^p` on `ℤ` for chain complexes (`ComplexShape.down ℤ`): the sign of
`1 ⊠ d` on `C_p ⊠ D_q` in a tensor product of complexes. -/
instance tensorSignsDownInt : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q + 1 = p) := by simp only [ComplexShape.down_Rel]; lia
  add_rel p q r (hpq : q + 1 = p) := by simp only [ComplexShape.down_Rel]; lia
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [Int.negOnePow_succ, neg_neg]

@[simp]
lemma ε_down_int (n : ℤ) : (ComplexShape.down ℤ).ε n = n.negOnePow := rfl

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

lemma map_zero_left {N N' : B} {V V' : E} (g : V ⟶ V') :
    P.tensor.map ((0 : N ⟶ N') ×ₘ g) = 0 := by
  simpa using P.map_smul_left 0 (0 : N ⟶ N') g

lemma map_zero_right {N N' : B} {V V' : E} (f : N ⟶ N') :
    P.tensor.map (f ×ₘ (0 : V ⟶ V')) = 0 := by
  simpa using P.map_smul_right 0 f (0 : V ⟶ V')

instance preservesZeroMorphisms_curry_obj (N : B) :
    ((Functor.curry.obj P.tensor).obj N).PreservesZeroMorphisms where
  map_zero _ _ := P.map_zero_right (𝟙 N)

instance preservesZeroMorphisms_curry :
    (Functor.curry.obj P.tensor).PreservesZeroMorphisms where
  map_zero N N' := by
    ext V
    exact P.map_zero_left (𝟙 V)

/-- `N ⊠ V` is a zero object when `N` is. -/
lemma isZero_tensor_left {N : B} (hN : IsZero N) (V : E) : IsZero (P.tensor.obj (N, V)) := by
  rw [IsZero.iff_id_eq_zero] at hN ⊢
  rw [← P.tensor.map_id, show 𝟙 (N, V) = 𝟙 N ×ₘ 𝟙 V from rfl, hN, P.map_zero_left]

/-- `N ⊠ V` is a zero object when `V` is. -/
lemma isZero_tensor_right (N : B) {V : E} (hV : IsZero V) : IsZero (P.tensor.obj (N, V)) := by
  rw [IsZero.iff_id_eq_zero] at hV ⊢
  rw [← P.tensor.map_id, show 𝟙 (N, V) = 𝟙 N ×ₘ 𝟙 V from rfl, hV, P.map_zero_right]

/-- The direct sums `⨁_{p+q=r} C_p ⊠ D_q` exist when `C` and `D` have finitely many nonzero
chain objects. -/
lemma hasMapBifunctor_of_finite {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    HomologicalComplex.HasMapBifunctor C D (Functor.curry.obj P.tensor)
      (ComplexShape.down ℤ) := by
  intro r
  refine hasCoproduct_of_finite _
    (((hC.prod hD).preimage Subtype.val_injective.injOn).subset ?_)
  rintro ⟨⟨p, q⟩, hpq⟩ hx
  exact ⟨fun hp => hx (P.isZero_tensor_left hp _), fun hq => hx (P.isZero_tensor_right _ hq)⟩

end DualityPairing

variable (P : DualityPairing B E B'')

/-- **Tensor product of complexes.** For complexes `C` in `B` and `D` in `E` with finitely many
nonzero chain objects, `C ⊗ D` has `(C ⊗ D)_r = ⨁_{p+q=r} C_p ⊠ D_q` and differential
`d ⊠ 1 + (-1)^p 1 ⊠ d` on `C_p ⊠ D_q`. -/
noncomputable def cxProd (C : ChainComplex B ℤ) (D : ChainComplex E ℤ)
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    ChainComplex B'' ℤ :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  C.mapBifunctor D (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)

/-- The chain map `f ⊗ g : C ⊗ D ⟶ C' ⊗ D'`, equal to `f_p ⊠ g_q` on `C_p ⊠ D_q`. -/
noncomputable def cxProdMap {C C' : ChainComplex B ℤ} {D D' : ChainComplex E ℤ}
    (f : C ⟶ C') (g : D ⟶ D') (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) (hC' : {r | ¬ IsZero (C'.X r)}.Finite)
    (hD' : {r | ¬ IsZero (D'.X r)}.Finite) :
    cxProd P C D hC hD ⟶ cxProd P C' D' hC' hD' :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  haveI := P.hasMapBifunctor_of_finite hC' hD'
  HomologicalComplex.mapBifunctorMap f g (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)

end HSP
