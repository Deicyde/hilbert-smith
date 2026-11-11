import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing

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
private lemma ε_down_int (n : ℤ) : (ComplexShape.down ℤ).ε n = n.negOnePow := rfl

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

private lemma map_zero_left {N N' : B} {V V' : E} (g : V ⟶ V') :
    P.tensor.map ((0 : N ⟶ N') ×ₘ g) = 0 := by
  simpa using P.map_smul_left 0 (0 : N ⟶ N') g

private lemma map_zero_right {N N' : B} {V V' : E} (f : N ⟶ N') :
    P.tensor.map (f ×ₘ (0 : V ⟶ V')) = 0 := by
  simpa using P.map_smul_right 0 f (0 : V ⟶ V')

instance additive_curry_obj (N : B) : ((Functor.curry.obj P.tensor).obj N).Additive where
  map_add {_ _ g g'} := by
    simpa [Functor.curry_obj_obj_map] using P.map_add_right (𝟙 N) g g'

instance additive_curry : (Functor.curry.obj P.tensor).Additive where
  map_add {_ _ f f'} := by
    ext V
    simpa [Functor.curry_obj_map_app] using P.map_add_left f f' (𝟙 V)

/-- `N ⊠ V` is a zero object when `N` is. -/
private lemma isZero_tensor_left {N : B} (hN : IsZero N) (V : E) :
    IsZero (P.tensor.obj (N, V)) := by
  rw [IsZero.iff_id_eq_zero] at hN ⊢
  rw [← P.tensor.map_id, show 𝟙 (N, V) = 𝟙 N ×ₘ 𝟙 V from rfl, hN, P.map_zero_left]

/-- `N ⊠ V` is a zero object when `V` is. -/
private lemma isZero_tensor_right (N : B) {V : E} (hV : IsZero V) :
    IsZero (P.tensor.obj (N, V)) := by
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
noncomputable abbrev cxProd (C : ChainComplex B ℤ) (D : ChainComplex E ℤ)
    (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) :
    ChainComplex B'' ℤ :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  C.mapBifunctor D (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)

/-- The chain map `f ⊗ g : C ⊗ D ⟶ C' ⊗ D'`, equal to `f_p ⊠ g_q` on `C_p ⊠ D_q`. -/
noncomputable abbrev cxProdMap {C C' : ChainComplex B ℤ} {D D' : ChainComplex E ℤ}
    (f : C ⟶ C') (g : D ⟶ D') (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) (hC' : {r | ¬ IsZero (C'.X r)}.Finite)
    (hD' : {r | ¬ IsZero (D'.X r)}.Finite) :
    cxProd P C D hC hD ⟶ cxProd P C' D' hC' hD' :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  haveI := P.hasMapBifunctor_of_finite hC' hD'
  HomologicalComplex.mapBifunctorMap f g (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)

namespace cxProd

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

/-- The pairs `(p, q)` with `p + q = r` where both `C_p` and `D_q` are nonzero: outside them the
summand `C_p ⊠ D_q` of `(C ⊗ D)_r` is a zero object. -/
noncomputable def supp (r : ℤ) : Finset (ℤ × ℤ) :=
  (hC.toFinset ×ˢ hD.toFinset).filter fun x => x.1 + x.2 = r

omit [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E] in
lemma mem_supp {r : ℤ} {x : ℤ × ℤ} :
    x ∈ supp hC hD r ↔ (¬ IsZero (C.X x.1) ∧ ¬ IsZero (D.X x.2)) ∧ x.1 + x.2 = r := by
  simp [supp]

/-- The inclusion of the summand `C_p ⊠ D_q` into `(C ⊗ D)_r` (zero unless `p + q = r`). -/
noncomputable abbrev ι (p q r : ℤ) : P.tensor.obj (C.X p, D.X q) ⟶ (cxProd P C D hC hD).X r :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  HomologicalComplex.ιMapBifunctorOrZero C D (Functor.curry.obj P.tensor) (ComplexShape.down ℤ)
    p q r

/-- The projection of `(C ⊗ D)_r` onto the summand `C_p ⊠ D_q` (zero unless `p + q = r`). -/
noncomputable def π (p q r : ℤ) : (cxProd P C D hC hD).X r ⟶ P.tensor.obj (C.X p, D.X q) :=
  haveI := P.hasMapBifunctor_of_finite hC hD
  HomologicalComplex.mapBifunctorDesc (K₁ := C) (K₂ := D) (F := Functor.curry.obj P.tensor)
    (c := ComplexShape.down ℤ) (j := r) fun p' q' _ =>
      if h : p' = p ∧ q' = q then eqToHom (by obtain ⟨rfl, rfl⟩ := h; rfl) else 0

lemma ι_π_self {p q r : ℤ} (h : p + q = r) : ι P hC hD p q r ≫ π P hC hD p q r = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, π,
    HomologicalComplex.ι_mapBifunctorDesc, dite_eq_left ⟨rfl, rfl⟩, eqToHom_refl]
  rfl

lemma ι_π_of_ne {p q p' q' r : ℤ} (hne : ¬ (p = p' ∧ q = q')) :
    ι P hC hD p q r ≫ π P hC hD p' q' r = 0 := by
  have := P.hasMapBifunctor_of_finite hC hD
  by_cases h : p + q = r
  · rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, π,
      HomologicalComplex.ι_mapBifunctorDesc, dite_eq_right hne]
  · rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h, zero_comp]

/-- `(C ⊗ D)_r` is the direct sum of its summands: `∑ π_{p,q} ≫ ι_{p,q} = 𝟙`. -/
lemma total (r : ℤ) :
    ∑ x ∈ supp hC hD r, π P hC hD x.1 x.2 r ≫ ι P hC hD x.1 x.2 r = 𝟙 _ := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext p q h
  change p + q = r at h
  rw [Preadditive.comp_sum, Category.comp_id]
  have hι : HomologicalComplex.ιMapBifunctor C D (Functor.curry.obj P.tensor)
      (ComplexShape.down ℤ) p q r h = ι P hC hD p q r :=
    (HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h).symm
  rw [hι]
  by_cases hx : (p, q) ∈ supp hC hD r
  · rw [Finset.sum_eq_single (p, q)]
    · rw [← Category.assoc, ι_π_self P hC hD h]
      exact Category.id_comp _
    · rintro ⟨p', q'⟩ _ hne
      rw [← Category.assoc, ι_π_of_ne P hC hD (fun h' => hne (by rw [h'.1, h'.2])), zero_comp]
    · exact fun h' => absurd hx h'
  · have hz : IsZero (P.tensor.obj (C.X p, D.X q)) := by
      rw [mem_supp] at hx
      by_cases hp : IsZero (C.X p)
      · exact P.isZero_tensor_left hp _
      · by_cases hq : IsZero (D.X q)
        · exact P.isZero_tensor_right _ hq
        · exact absurd ⟨⟨hp, hq⟩, h⟩ hx
    rw [hz.eq_of_src (ι P hC hD p q r) 0, Finset.sum_eq_zero fun _ _ => zero_comp]

/-- Morphisms into `(C ⊗ D)_r` agree when their projections to every summand agree. -/
lemma hom_ext_to {r : ℤ} {Z : B''} {f g : Z ⟶ (cxProd P C D hC hD).X r}
    (h : ∀ p q, p + q = r → f ≫ π P hC hD p q r = g ≫ π P hC hD p q r) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← total P hC hD r, Preadditive.comp_sum,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Category.assoc, ← Category.assoc, h x.1 x.2 ((mem_supp hC hD).1 hx).2]

private lemma dualHom_sum {M N : B''} {ι' : Type*} (s : Finset ι') (f : ι' → (M ⟶ N)) :
    DualCat.dualHom (∑ i ∈ s, f i) = ∑ i ∈ s, DualCat.dualHom (f i) :=
  map_sum (AddMonoidHom.mk' (DualCat.dualHom (M := M) (N := N)) DualCat.dualHom_add) f s

/-- Morphisms out of `((C ⊗ D)_r)^*` agree when they agree on the dual of every summand. -/
lemma dual_hom_ext {r : ℤ} {Z : B''} {f g : DualCat.dual ((cxProd P C D hC hD).X r) ⟶ Z}
    (h : ∀ p q, p + q = r →
      DualCat.dualHom (π P hC hD p q r) ≫ f = DualCat.dualHom (π P hC hD p q r) ≫ g) :
    f = g := by
  have h1 : 𝟙 (DualCat.dual ((cxProd P C D hC hD).X r)) =
      ∑ x ∈ supp hC hD r, DualCat.dualHom (ι P hC hD x.1 x.2 r) ≫
        DualCat.dualHom (π P hC hD x.1 x.2 r) := by
    rw [← DualCat.dualHom_id, ← total P hC hD r, dualHom_sum]
    simp only [DualCat.dualHom_comp]
  rw [← Category.id_comp f, ← Category.id_comp g, h1, Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, Category.assoc, h x.1 x.2 ((mem_supp hC hD).1 hx).2]

end cxProd

end HSP
