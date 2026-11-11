import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LTheory.Base.Groups.SumOfFunctors
import HilbertSmithPaper.LTheory.Base.Groups.UnitaryInvariance

/-!
# Sums of functors on L^p

For duality functors `F, G : A → A'`, `(F ⊕ G)_* = F_* + G_*` on `L^p_k(A)`. The completion
`Kar(F ⊕ G)` sends `(M, e)` to `(F M ⊕ G M, F e ⊕ G e)`, and the canonical isomorphism to the sum
`(F M, F e) ⊕ (G M, G e)` in `Kar A'` is a unitary natural isomorphism
`Kar(F ⊕ G) ≅ Kar F ⊕ Kar G`. Conclude by unitary invariance and sums of functors.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

namespace LpMapBiprod

variable (F G : DualFunctor A A')

omit [Linear ℚ A'] [HasFiniteBiproducts A'] [DualCat A'] in
private lemma add_f {P Q : Karoubi A'} (f g : P ⟶ Q) : (f + g).f = f.f + g.f := rfl

omit [Linear ℚ A'] [HasFiniteBiproducts A'] [DualCat A'] in
private lemma zero_f {P Q : Karoubi A'} : (0 : P ⟶ Q).f = 0 := rfl

/-- The projection `Kar(F ⊕ G)(M, e) → Kar F (M, e)`, `π ∘ (F e ⊕ G e) = F e ∘ π`. -/
private noncomputable def fstK (P : Karoubi A) :
    (F.biprod G).kar.toFunctor.obj P ⟶ F.kar.toFunctor.obj P :=
  ⟨biprod.fst ≫ F.toFunctor.map P.p, by
    change biprod.map (F.toFunctor.map P.p) (G.toFunctor.map P.p) ≫
      (biprod.fst ≫ F.toFunctor.map P.p) ≫ F.toFunctor.map P.p = biprod.fst ≫ F.toFunctor.map P.p
    simp only [biprod.map_fst_assoc, Category.assoc, ← Functor.map_comp, P.idem]⟩

/-- The projection `Kar(F ⊕ G)(M, e) → Kar G (M, e)`. -/
private noncomputable def sndK (P : Karoubi A) :
    (F.biprod G).kar.toFunctor.obj P ⟶ G.kar.toFunctor.obj P :=
  ⟨biprod.snd ≫ G.toFunctor.map P.p, by
    change biprod.map (F.toFunctor.map P.p) (G.toFunctor.map P.p) ≫
      (biprod.snd ≫ G.toFunctor.map P.p) ≫ G.toFunctor.map P.p = biprod.snd ≫ G.toFunctor.map P.p
    simp only [biprod.map_snd_assoc, Category.assoc, ← Functor.map_comp, P.idem]⟩

/-- The inclusion `Kar F (M, e) → Kar(F ⊕ G)(M, e)`. -/
private noncomputable def inlK (P : Karoubi A) :
    F.kar.toFunctor.obj P ⟶ (F.biprod G).kar.toFunctor.obj P :=
  ⟨F.toFunctor.map P.p ≫ biprod.inl, by
    change F.toFunctor.map P.p ≫ (F.toFunctor.map P.p ≫ biprod.inl) ≫
      biprod.map (F.toFunctor.map P.p) (G.toFunctor.map P.p) = F.toFunctor.map P.p ≫ biprod.inl
    simp only [biprod.inl_map, Category.assoc]
    simp only [← Category.assoc, ← Functor.map_comp, P.idem]⟩

/-- The inclusion `Kar G (M, e) → Kar(F ⊕ G)(M, e)`. -/
private noncomputable def inrK (P : Karoubi A) :
    G.kar.toFunctor.obj P ⟶ (F.biprod G).kar.toFunctor.obj P :=
  ⟨G.toFunctor.map P.p ≫ biprod.inr, by
    change G.toFunctor.map P.p ≫ (G.toFunctor.map P.p ≫ biprod.inr) ≫
      biprod.map (F.toFunctor.map P.p) (G.toFunctor.map P.p) = G.toFunctor.map P.p ≫ biprod.inr
    simp only [biprod.inr_map, Category.assoc]
    simp only [← Category.assoc, ← Functor.map_comp, P.idem]⟩

omit [Linear ℚ A'] [DualCat A'] in
private lemma total_idem {X Y : A'} (e : X ⟶ X) (e' : Y ⟶ Y) (he : e ≫ e = e) (he' : e' ≫ e' = e') :
    (biprod.fst ≫ e) ≫ e ≫ biprod.inl + (biprod.snd ≫ e') ≫ e' ≫ biprod.inr = biprod.map e e' := by
  apply biprod.hom_ext' <;>
    simp [Preadditive.comp_add, ← Category.assoc, he, he']

omit [Linear ℚ A'] [DualCat A'] in
private lemma inl_fst_idem {X Y : A'} (e : X ⟶ X) (he : e ≫ e = e) :
    (e ≫ (biprod.inl : X ⟶ X ⊞ Y)) ≫ biprod.fst ≫ e = e := by
  simp [he]

omit [Linear ℚ A'] [DualCat A'] in
private lemma inr_snd_idem {X Y : A'} (e' : Y ⟶ Y) (he' : e' ≫ e' = e') :
    (e' ≫ (biprod.inr : Y ⟶ X ⊞ Y)) ≫ biprod.snd ≫ e' = e' := by
  simp [he']

omit [Linear ℚ A'] [DualCat A'] in
private lemma inl_snd_idem {X Y : A'} (e : X ⟶ X) (e' : Y ⟶ Y) :
    (e ≫ (biprod.inl : X ⟶ X ⊞ Y)) ≫ biprod.snd ≫ e' = 0 := by
  simp

omit [Linear ℚ A'] [DualCat A'] in
private lemma inr_fst_idem {X Y : A'} (e : X ⟶ X) (e' : Y ⟶ Y) :
    (e' ≫ (biprod.inr : Y ⟶ X ⊞ Y)) ≫ biprod.fst ≫ e = 0 := by
  simp

/-- `Kar(F ⊕ G)(M, e) ≅ Kar F (M, e) ⊕ Kar G (M, e)`. -/
private noncomputable def isoK (P : Karoubi A) :
    (F.biprod G).kar.toFunctor.obj P ≅ F.kar.toFunctor.obj P ⊞ G.kar.toFunctor.obj P where
  hom := biprod.lift (fstK F G P) (sndK F G P)
  inv := biprod.desc (inlK F G P) (inrK F G P)
  hom_inv_id := by
    rw [biprod.lift_desc]
    apply Karoubi.hom_ext
    rw [add_f, Karoubi.comp_f, Karoubi.comp_f, Karoubi.id_f]
    change (biprod.fst ≫ F.toFunctor.map P.p) ≫ F.toFunctor.map P.p ≫ biprod.inl +
      (biprod.snd ≫ G.toFunctor.map P.p) ≫ G.toFunctor.map P.p ≫ biprod.inr =
        biprod.map (F.toFunctor.map P.p) (G.toFunctor.map P.p)
    exact total_idem _ _ (by rw [← Functor.map_comp, P.idem]) (by rw [← Functor.map_comp, P.idem])
  inv_hom_id := by
    have hF : F.toFunctor.map P.p ≫ F.toFunctor.map P.p = F.toFunctor.map P.p := by
      rw [← Functor.map_comp, P.idem]
    have hG : G.toFunctor.map P.p ≫ G.toFunctor.map P.p = G.toFunctor.map P.p := by
      rw [← Functor.map_comp, P.idem]
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.lift_fst, biprod.lift_snd,
        Category.assoc, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
        Category.comp_id] <;>
      apply Karoubi.hom_ext <;>
      simp only [Karoubi.comp_f, zero_f, Karoubi.id_f]
    · exact inl_fst_idem (Y := G.toFunctor.obj P.X) _ hF
    · exact inl_snd_idem _ _
    · exact inr_fst_idem _ _
    · exact inr_snd_idem (X := F.toFunctor.obj P.X) _ hG

omit [Linear ℚ A'] [DualCat A'] in
private lemma nat_fst {X Y X' Y' : A'} (a : X ⟶ X') (b : Y ⟶ Y') (p : X ⟶ X) (q : X' ⟶ X')
    (h₁ : a ≫ q = a) (h₂ : p ≫ a = a) :
    biprod.map a b ≫ biprod.fst ≫ q = (biprod.fst ≫ p) ≫ a := by
  rw [biprod.map_fst_assoc, h₁, Category.assoc, h₂]

omit [Linear ℚ A'] [DualCat A'] in
private lemma nat_snd {X Y X' Y' : A'} (a : X ⟶ X') (b : Y ⟶ Y') (p : Y ⟶ Y) (q : Y' ⟶ Y')
    (h₁ : b ≫ q = b) (h₂ : p ≫ b = b) :
    biprod.map a b ≫ biprod.snd ≫ q = (biprod.snd ≫ p) ≫ b := by
  rw [biprod.map_snd_assoc, h₁, Category.assoc, h₂]

private lemma key (H : DualFunctor A A') {M : A} (e : M ⟶ M) (he : e ≫ e = e) {Z : A'}
    (g : Z ⟶ H.toFunctor.obj M) :
    H.toFunctor.map (dualHom e) ≫ H.toFunctor.map (dualHom e) ≫ (H.ξ M).hom ≫
      dualHom (g ≫ H.toFunctor.map e) =
        H.toFunctor.map (dualHom e) ≫ (H.ξ M).hom ≫ dualHom g := by
  have h₁ : H.toFunctor.map (dualHom e) ≫ H.toFunctor.map (dualHom e) =
      H.toFunctor.map (dualHom e) := by
    rw [← Functor.map_comp, ← dualHom_comp, he]
  have h₂ : dualHom (H.toFunctor.map e) ≫ dualHom (H.toFunctor.map e) =
      dualHom (H.toFunctor.map e) := by
    rw [← dualHom_comp, ← Functor.map_comp, he]
  rw [dualHom_comp, reassoc_of% h₁, reassoc_of% (H.ξ_natural e), reassoc_of% h₂,
    ← reassoc_of% (H.ξ_natural e)]

private lemma unitary_f {M : A} (e : M ⟶ M) (he : e ≫ e = e) :
    (biprod.fst ≫ F.toFunctor.map (dualHom e)) ≫ (F.toFunctor.map (dualHom e) ≫ (F.ξ M).hom) ≫
        dualHom (biprod.fst ≫ F.toFunctor.map e) +
      (biprod.snd ≫ G.toFunctor.map (dualHom e)) ≫ (G.toFunctor.map (dualHom e) ≫ (G.ξ M).hom) ≫
        dualHom (biprod.snd ≫ G.toFunctor.map e) =
      (F.biprod G).toFunctor.map (dualHom e) ≫ ((F.biprod G).ξ M).hom := by
  have hR : (F.biprod G).toFunctor.map (dualHom e) ≫ ((F.biprod G).ξ M).hom =
      biprod.lift (biprod.fst ≫ F.toFunctor.map (dualHom e))
        (biprod.snd ≫ G.toFunctor.map (dualHom e)) ≫
          ((F.biprod G).ξ M).hom ≫ dualHom (biprod.lift biprod.fst biprod.snd) := by
    have h₁ : (biprod.lift biprod.fst biprod.snd :
        F.toFunctor.obj M ⊞ G.toFunctor.obj M ⟶ F.toFunctor.obj M ⊞ G.toFunctor.obj M) = 𝟙 _ := by
      apply biprod.hom_ext <;> simp
    have h₂ : biprod.lift (biprod.fst ≫ F.toFunctor.map (dualHom e))
        (biprod.snd ≫ G.toFunctor.map (dualHom e)) = (F.biprod G).toFunctor.map (dualHom e) := by
      rw [DualFunctor.biprod_map]
      apply biprod.hom_ext <;> simp
    rw [h₁, h₂]
    erw [dualHom_id, Category.comp_id]
    rfl
  rw [hR, DualFunctor.lift_biprod_ξ_dualHom_lift]
  simp only [Category.assoc]
  rw [key F e he, key G e he]
  rfl

/-- The unitary natural isomorphism `Kar(F ⊕ G) ≅ Kar F ⊕ Kar G`. -/
private noncomputable def karBiprod :
    DualFunctor.UnitaryIso (F.biprod G).kar (F.kar.biprod G.kar) where
  iso := NatIso.ofComponents (isoK F G) (fun {P Q} f => by
    change (F.biprod G).kar.toFunctor.map f ≫ biprod.lift (fstK F G Q) (sndK F G Q) =
      biprod.lift (fstK F G P) (sndK F G P) ≫
        biprod.map (F.kar.toFunctor.map f) (G.kar.toFunctor.map f)
    have hc : ∀ H : DualFunctor A A', H.toFunctor.map f.f ≫ H.toFunctor.map Q.p =
        H.toFunctor.map f.f := fun H => by rw [← H.toFunctor.map_comp, Karoubi.comp_p]
    have hp : ∀ H : DualFunctor A A', H.toFunctor.map P.p ≫ H.toFunctor.map f.f =
        H.toFunctor.map f.f := fun H => by rw [← H.toFunctor.map_comp, Karoubi.p_comp]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst, ← Category.assoc,
        biprod.lift_fst]
      apply Karoubi.hom_ext
      exact nat_fst _ _ _ _ (hc _) (hp _)
    · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd, ← Category.assoc,
        biprod.lift_snd]
      apply Karoubi.hom_ext
      exact nat_snd _ _ _ _ (hc _) (hp _))
  unitary P := by
    change biprod.lift (fstK F G (dual P)) (sndK F G (dual P)) ≫
      ((F.kar.biprod G.kar).ξ P).hom ≫ dualHom (biprod.lift (fstK F G P) (sndK F G P)) = _
    rw [DualFunctor.lift_biprod_ξ_dualHom_lift]
    apply Karoubi.hom_ext
    exact unitary_f F G P.p P.idem

end LpMapBiprod

open LpMapBiprod in
/-- **Sums of functors on L^p.** `(F ⊕ G)_* = F_* + G_*` on `L^p_k(A)`. -/
theorem Lp.map_biprod (F G : DualFunctor A A') (k : ℤ) :
    Lp.map (F.biprod G) k = Lp.map F k + Lp.map G k := by
  change LGroup.map (F.biprod G).kar k = LGroup.map F.kar k + LGroup.map G.kar k
  rw [LGroup.map_eq_of_unitaryIso (karBiprod F G), LGroup.map_biprod]

end HSP
