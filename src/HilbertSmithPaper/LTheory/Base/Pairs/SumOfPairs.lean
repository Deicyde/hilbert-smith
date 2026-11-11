import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare

/-!
# Sums of pairs

If `(f : C ⟶ D, δφ, φ)` and `(f' : C' ⟶ D', δφ', φ')` are strict `n`-dimensional Poincaré
pairs, then so is `(f ⊕ f' : C ⊞ C' ⟶ D ⊞ D', δφ ⊕ δφ', φ ⊕ φ')`.

The boundary is the sum of the boundaries. The cone of `f ⊕ f'` is isomorphic to
`𝒞(f) ⊞ 𝒞(f')` through the maps of cones induced by the biproduct maps, and under this
isomorphism and `(D ⊞ D')^{n-*} ≅ D^{n-*} ⊞ D'^{n-*}` the pair map of the sum is `ψ ⊕ ψ'`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace SymPair

omit [Linear ℚ B] [DualCat B] in
private lemma isZero_biprod {X Y : B} (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⊞ Y) := by
  rw [IsZero.iff_id_eq_zero, ← biprod.total, hX.eq_of_tgt biprod.fst 0,
    hY.eq_of_tgt biprod.snd 0, zero_comp, zero_comp, add_zero]

private lemma dualCx_map_add {C D : ChainComplex B ℤ} (f g : C ⟶ D) (n : ℤ) :
    dualCx.map (f + g) n = dualCx.map f n + dualCx.map g n := by
  ext r
  simp

private lemma dualCx_map_zero (C D : ChainComplex B ℤ) (n : ℤ) :
    dualCx.map (0 : C ⟶ D) n = 0 := by
  ext r
  simp

/-- The canonical isomorphism `(C ⊞ C')^{n-*} ≅ C^{n-*} ⊞ C'^{n-*}`. -/
private noncomputable def dualBiprodIso (C C' : ChainComplex B ℤ) (n : ℤ) :
    dualCx (C ⊞ C') n ≅ dualCx C n ⊞ dualCx C' n where
  hom := biprod.lift (dualCx.map biprod.inl n) (dualCx.map biprod.inr n)
  inv := biprod.desc (dualCx.map biprod.fst n) (dualCx.map biprod.snd n)
  hom_inv_id := by
    rw [biprod.lift_desc, ← dualCx.map_comp, ← dualCx.map_comp, ← dualCx_map_add,
      biprod.total, dualCx.map_id]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [← dualCx.map_comp, dualCx.map_id, dualCx_map_zero]

/-- Sums of chain homotopy equivalences are chain homotopy equivalences. -/
private noncomputable def biprodHomotopyEquiv {X X' Y Y' : ChainComplex B ℤ}
    (e : HomotopyEquiv X Y) (e' : HomotopyEquiv X' Y') : HomotopyEquiv (X ⊞ X') (Y ⊞ Y') where
  hom := biprod.map e.hom e'.hom
  inv := biprod.map e.inv e'.inv
  homotopyHomInvId := (Homotopy.ofEq (by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp)).trans
    ((((e.homotopyHomInvId.compRight biprod.inl).compLeft biprod.fst).add
      ((e'.homotopyHomInvId.compRight biprod.inr).compLeft biprod.snd)).trans
      (Homotopy.ofEq (by simp [biprod.total])))
  homotopyInvHomId := (Homotopy.ofEq (by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp)).trans
    ((((e.homotopyInvHomId.compRight biprod.inl).compLeft biprod.fst).add
      ((e'.homotopyInvHomId.compRight biprod.inr).compLeft biprod.snd)).trans
      (Homotopy.ofEq (by simp [biprod.total])))

/-- The map of cones `𝒞(f) ⟶ 𝒞(f₁)`, `(y, x) ↦ (b y, a x)`, of a commutative square
`f ≫ b = a ≫ f₁`. -/
private noncomputable def coneMap {C D C₁ D₁ : ChainComplex B ℤ} {f : C ⟶ D} {f₁ : C₁ ⟶ D₁}
    (a : C ⟶ C₁) (b : D ⟶ D₁) (w : f ≫ b = a ≫ f₁) : cone f ⟶ cone f₁ where
  f r := biprod.map (b.f r) (a.f (r - 1))
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    obtain rfl : j = i - 1 := by omega
    change _ ≫ cone.d _ i (i - 1) = cone.d _ i (i - 1) ≫ _
    simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id]
    have w' : f.f (i - 1) ≫ b.f (i - 1) = a.f (i - 1) ≫ f₁.f (i - 1) := by
      rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f]
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [w']

/-- `𝒞(f ⊕ f') ≅ 𝒞(f) ⊞ 𝒞(f')`. -/
private noncomputable def coneBiprodIso {C D C' D' : ChainComplex B ℤ} (f : C ⟶ D)
    (f' : C' ⟶ D') : cone (biprod.map f f') ≅ cone f ⊞ cone f' where
  hom := biprod.lift (coneMap biprod.fst biprod.fst (biprod.map_fst _ _))
    (coneMap biprod.snd biprod.snd (biprod.map_snd _ _))
  inv := biprod.desc (coneMap biprod.inl biprod.inl (biprod.inl_map _ _).symm)
    (coneMap biprod.inr biprod.inr (biprod.inr_map _ _).symm)
  hom_inv_id := by
    rw [biprod.lift_desc]
    refine HomologicalComplex.hom_ext _ _ fun r => ?_
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [coneMap]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      refine HomologicalComplex.hom_ext _ _ fun r => ?_ <;>
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [coneMap]

/-- The sum of two strict `n`-dimensional Poincaré pairs is a strict `n`-dimensional
Poincaré pair. -/
theorem sum {m n : ℤ} (W W' : SymPair B m n) :
    ∃ W'' : SymPair B m n, W''.data = ⟨W.C ⊞ W'.C, W.D ⊞ W'.D, biprod.map W.f W'.f,
      StructureCx.sum W.δφ W'.δφ, StructureCx.sum W.φ W'.φ⟩ := by
  obtain ⟨⟨zC, zφ, zbounded, zcycle, zsymmetric, zpoincare⟩, hz⟩ :=
    SymPoincare.exists_sum W.boundary W'.boundary
  obtain ⟨rfl, hz⟩ := Sigma.mk.inj_iff.mp hz
  obtain rfl := eq_of_heq hz
  have hrel : (StructureCx (W.D ⊞ W'.D)).d n m (StructureCx.sum W.δφ W'.δφ) =
      (StructureCx.push (biprod.map W.f W'.f)).f m (StructureCx.sum W.φ W'.φ) := by
    rw [StructureCx.sum, StructureCx.sum, map_add, map_add, StructureCx.d_push_apply,
      StructureCx.d_push_apply, W.rel, W'.rel]
    simp only [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← StructureCx.push_comp,
      biprod.inl_map, biprod.inr_map]
  refine ⟨
    { C := W.C ⊞ W'.C
      D := W.D ⊞ W'.D
      f := biprod.map W.f W'.f
      δφ := StructureCx.sum W.δφ W'.δφ
      φ := StructureCx.sum W.φ W'.φ
      dim := W.dim
      boundary_bounded := zbounded
      boundary_cycle := zcycle
      boundary_symmetric := zsymmetric
      boundary_poincare := zpoincare
      bounded := fun r hr => IsZero.of_iso
        (isZero_biprod (W.bounded r hr) (W'.bounded r hr))
        (HomologicalComplex.biprodXIso W.D W'.D r)
      symmetric := by
        rw [StructureCx.sum, map_add, StructureCx.T_push_apply, StructureCx.T_push_apply,
          W.symmetric, W'.symmetric]
      rel := hrel
      poincare := ?_ }, rfl⟩
  obtain ⟨e, he⟩ := W.poincare
  obtain ⟨e', he'⟩ := W'.poincare
  refine ⟨(HomotopyEquiv.ofIso (dualBiprodIso W.D W'.D n)).trans
    ((biprodHomotopyEquiv e e').trans
      (HomotopyEquiv.ofIso (coneBiprodIso W.f W'.f).symm)), ?_⟩
  have hm : ∀ {Z X Y X' Y' : ChainComplex B ℤ} (A : Z ⟶ X) (A' : Z ⟶ X') (ψ : X ⟶ Y)
      (ψ' : X' ⟶ Y'), biprod.lift A A' ≫ biprod.map ψ ψ' = biprod.lift (A ≫ ψ) (A' ≫ ψ') :=
    fun A A' ψ ψ' => by apply biprod.hom_ext <;> simp
  change biprod.lift (dualCx.map biprod.inl n) (dualCx.map biprod.inr n) ≫
    biprod.map e.hom e'.hom ≫ biprod.desc (coneMap biprod.inl biprod.inl (biprod.inl_map _ _).symm)
      (coneMap biprod.inr biprod.inr (biprod.inr_map _ _).symm) = _
  rw [he, he', ← Category.assoc, hm, biprod.lift_desc]
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · simp [coneMap, pairMap]
    rw [StructureCx.sum, Pi.add_apply, StructureCx.push_apply, StructureCx.push_apply]
  · simp [coneMap, pairMap]
    have hl : dualHom ((biprod.map W.f W'.f).f (n - r)) ≫
        dualHom ((biprod.inl : W.C ⟶ W.C ⊞ W'.C).f (n - r)) =
        dualHom ((biprod.inl : W.D ⟶ W.D ⊞ W'.D).f (n - r)) ≫ dualHom (W.f.f (n - r)) := by
      rw [← dualHom_comp, ← dualHom_comp, ← HomologicalComplex.comp_f, biprod.inl_map,
        HomologicalComplex.comp_f]
    have hr : dualHom ((biprod.map W.f W'.f).f (n - r)) ≫
        dualHom ((biprod.inr : W'.C ⟶ W.C ⊞ W'.C).f (n - r)) =
        dualHom ((biprod.inr : W'.D ⟶ W.D ⊞ W'.D).f (n - r)) ≫ dualHom (W'.f.f (n - r)) := by
      rw [← dualHom_comp, ← dualHom_comp, ← HomologicalComplex.comp_f, biprod.inr_map,
        HomologicalComplex.comp_f]
    rw [StructureCx.sum, Pi.add_apply, StructureCx.push_apply, StructureCx.push_apply,
      Preadditive.comp_add, smul_add, reassoc_of% hl, reassoc_of% hr]

end SymPair

end HSP
