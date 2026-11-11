import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolutionSquare
import HilbertSmithPaper.LTheory.Base.Complexes.DualHomotopyEquivalence
import HilbertSmithPaper.LTheory.Base.Complexes.ShiftEquivalence

/-!
# Homotopy-isometric complexes are cobordant

Let `P` be a class of objects closed under sums of two objects (the cone point of any biproduct
bicone of two objects of `P` is in `P`), `(C, φ)`,
`(C', φ')` strict `k`-dimensional symmetric Poincaré complexes with chain objects in `P`,
`h : C ⟶ C'` a chain homotopy equivalence and `χ ∈ M(C')_{k+1}` with `∂χ = h_% φ - φ'`. With
`χ' = (χ + Tχ)/2`, `((h, 1) : C ⊞ C' ⟶ C', χ', φ ⊕ (-φ'))` is a strict `(k+1)`-dimensional
Poincaré pair whose chain objects lie in `P`; its boundary is `(C ⊞ C', φ ⊕ (-φ'))`.

Proof of the Poincaré condition. With `g = (h, 1)`, the projection `π : 𝒞(g) ⟶ ΣC`,
`(x, (y, y')) ↦ y`, is a chain homotopy equivalence with inverse `σ : y ↦ (0, (y, -h y))`:
`π σ = 1` and `1 - σ π = dH + Hd` for `H(x, (y, y')) = (0, (0, (-1)^r x))`. Moreover
`π ψ = Σ(φ_♮ ∘ h^{k-*}) ∘ ε` with the isomorphism `ε_r = (-1)^r : C'^{k+1-*} ⟶ Σ C'^{k-*}`; so
`π ψ` is an equivalence, and `ψ ≃ σ π ψ` is one too.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat ZeroObject

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace Cylinder

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {X Y : ChainComplex V ℤ}

@[reassoc (attr := simp)]
private lemma inl_fst_f (r : ℤ) :
    (biprod.inl : X ⟶ X ⊞ Y).f r ≫ (biprod.fst : X ⊞ Y ⟶ X).f r = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]

@[reassoc (attr := simp)]
private lemma inr_snd_f (r : ℤ) :
    (biprod.inr : Y ⟶ X ⊞ Y).f r ≫ (biprod.snd : X ⊞ Y ⟶ Y).f r = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]

@[reassoc (attr := simp)]
private lemma inl_snd_f (r : ℤ) :
    (biprod.inl : X ⟶ X ⊞ Y).f r ≫ (biprod.snd : X ⊞ Y ⟶ Y).f r = 0 := by
  rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]

@[reassoc (attr := simp)]
private lemma inr_fst_f (r : ℤ) :
    (biprod.inr : Y ⟶ X ⊞ Y).f r ≫ (biprod.fst : X ⊞ Y ⟶ X).f r = 0 := by
  rw [← HomologicalComplex.comp_f, biprod.inr_fst, HomologicalComplex.zero_f]

@[reassoc (attr := simp)]
private lemma inl_desc_f {Z : ChainComplex V ℤ} (a : X ⟶ Z) (b : Y ⟶ Z) (r : ℤ) :
    (biprod.inl : X ⟶ X ⊞ Y).f r ≫ (biprod.desc a b).f r = a.f r := by
  rw [← HomologicalComplex.comp_f, biprod.inl_desc]

@[reassoc (attr := simp)]
private lemma inr_desc_f {Z : ChainComplex V ℤ} (a : X ⟶ Z) (b : Y ⟶ Z) (r : ℤ) :
    (biprod.inr : Y ⟶ X ⊞ Y).f r ≫ (biprod.desc a b).f r = b.f r := by
  rw [← HomologicalComplex.comp_f, biprod.inr_desc]

private lemma total_f (r : ℤ) :
    (biprod.fst : X ⊞ Y ⟶ X).f r ≫ (biprod.inl : X ⟶ X ⊞ Y).f r +
      (biprod.snd : X ⊞ Y ⟶ Y).f r ≫ (biprod.inr : Y ⟶ X ⊞ Y).f r = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply,
    biprod.total, HomologicalComplex.id_f]

/-- The chain objects of `X ⊞ Y` are sums of those of `X` and `Y`: the components of the
biproduct maps form a biproduct bicone. -/
private noncomputable def bicone (r : ℤ) : BinaryBicone (X.X r) (Y.X r) where
  pt := (X ⊞ Y).X r
  fst := (biprod.fst : X ⊞ Y ⟶ X).f r
  snd := (biprod.snd : X ⊞ Y ⟶ Y).f r
  inl := (biprod.inl : X ⟶ X ⊞ Y).f r
  inr := (biprod.inr : Y ⟶ X ⊞ Y).f r
  inl_fst := inl_fst_f r
  inl_snd := inl_snd_f r
  inr_fst := inr_fst_f r
  inr_snd := inr_snd_f r

private noncomputable def bicone_isBilimit (r : ℤ) : (bicone (X := X) (Y := Y) r).IsBilimit :=
  isBinaryBilimitOfTotal _ (total_f r)

private lemma desc_f {C C' : ChainComplex V ℤ} (h : C ⟶ C') (r : ℤ) :
    (biprod.desc h (𝟙 C')).f r =
      (biprod.fst : C ⊞ C' ⟶ C).f r ≫ h.f r + (biprod.snd : C ⊞ C' ⟶ C').f r := by
  rw [biprod.desc_eq, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.comp_id]

section Projection

variable [HasZeroObject V] {C C' : ChainComplex V ℤ}

omit [HasBinaryBiproducts V] in
private lemma isZero_zeroX (r : ℤ) : IsZero ((0 : ChainComplex V ℤ).X r) :=
  (HomologicalComplex.eval V _ r).map_isZero (isZero_zero _)

/-- The projection `π : 𝒞((h, 1)) ⟶ ΣC`, `(x, (y, y')) ↦ y`. -/
private noncomputable def proj (h : C ⟶ C') : cone (biprod.desc h (𝟙 C')) ⟶ cone.shift C where
  f r := biprod.lift 0 (biprod.snd ≫ (biprod.fst : C ⊞ C' ⟶ C).f (r - 1))
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    obtain rfl : j = i - 1 := by omega
    change _ ≫ cone.d _ i (i - 1) = cone.d _ i (i - 1) ≫ _
    simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id]
    apply biprod.hom_ext
    · exact (isZero_zeroX (i - 1)).eq_of_tgt _ _
    · simp

/-- The section `σ : ΣC ⟶ 𝒞((h, 1))`, `y ↦ (0, (y, -h y))`. -/
private noncomputable def sect (h : C ⟶ C') : cone.shift C ⟶ cone (biprod.desc h (𝟙 C')) where
  f r := biprod.lift 0 (biprod.snd ≫ ((biprod.inl : C ⟶ C ⊞ C').f (r - 1) -
    h.f (r - 1) ≫ (biprod.inr : C' ⟶ C ⊞ C').f (r - 1)))
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    obtain rfl : j = i - 1 := by omega
    change _ ≫ cone.d _ i (i - 1) = cone.d _ i (i - 1) ≫ _
    simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id]
    apply biprod.hom_ext
    · simp
    · simp

private lemma sect_proj (h : C ⟶ C') : sect h ≫ proj h = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · exact (isZero_zeroX r).eq_of_tgt _ _
  · simp [proj, sect]

/-- `1 - σ π = dH + Hd` for `H(x, (y, y')) = (0, (0, (-1)^r x))`. -/
private noncomputable def projSect (h : C ⟶ C') : Homotopy (𝟙 _) (proj h ≫ sect h) := by
  refine Homotopy.equivSubZero.symm ((Homotopy.ofEq ?_).trans (Homotopy.nullHomotopy'
    (fun i j hij => biprod.fst ≫ (i.negOnePow • ((C'.XIsoOfEq (show i = j - 1 by
      simp only [ComplexShape.down_Rel] at hij; omega)).hom ≫
        (biprod.inr : C' ⟶ C ⊞ C').f (j - 1))) ≫ biprod.inr)))
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  rw [Homotopy.nullHomotopicMap'_f (k₂ := r + 1) (k₀ := r - 1) (by simp) (by simp),
    HomologicalComplex.sub_f_apply]
  change _ = cone.d _ r (r - 1) ≫ _ + _ ≫ cone.d _ (r + 1) r
  simp only [cone.d, dite_true, dite_eq_left (show r + 1 - 1 = r by omega)]
  apply biprod.hom_ext <;> apply biprod.hom_ext'
  · simp [proj, sect, smul_smul, Int.units_mul_self]
  · simp [proj, sect]
  · simp only [proj, sect]
    simp
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, Units.neg_smul, neg_add_cancel]
  · simp only [proj, sect]
    simp [smul_smul, Int.units_mul_self, desc_f]
    rw [← total_f (X := C) (Y := C') (r - 1)]
    abel

/-- `π` is a chain homotopy equivalence with inverse `σ`. -/
private noncomputable def projEquiv (h : C ⟶ C') :
    HomotopyEquiv (cone.shift C) (cone (biprod.desc h (𝟙 C'))) where
  hom := sect h
  inv := proj h
  homotopyHomInvId := Homotopy.ofEq (sect_proj h)
  homotopyInvHomId := (projSect h).symm

end Projection

/-- A chain map homotopic to a chain homotopy equivalence is one. -/
private noncomputable def ofHomotopic {X Y : ChainComplex V ℤ} (e : HomotopyEquiv X Y)
    (f : X ⟶ Y) (H : Homotopy e.hom f) : HomotopyEquiv X Y where
  hom := f
  inv := e.inv
  homotopyHomInvId := (H.symm.compRight e.inv).trans e.homotopyHomInvId
  homotopyInvHomId := (H.symm.compLeft e.inv).trans e.homotopyInvHomId

end Cylinder

namespace Cylinder

private lemma eqToHom_dualHom_d (D : ChainComplex B ℤ) {a a' b b' : ℤ} (ha : a = a')
    (hb : b = b') :
    eqToHom (congrArg (fun i => dual (D.X i)) hb) ≫ dualHom (D.d a' b') =
      dualHom (D.d a b) ≫ eqToHom (congrArg (fun i => dual (D.X i)) ha) := by
  subst ha hb
  simp

/-- `ε_r = (-1)^r : (C^{k+1-*})_r ⟶ (Σ C^{k-*})_r`. -/
private noncomputable def epsX (D : ChainComplex B ℤ) (k r : ℤ) :
    dual (D.X (k + 1 - r)) ≅ (0 : ChainComplex B ℤ).X r ⊞ dual (D.X (k - (r - 1))) where
  hom := biprod.lift 0 (r.negOnePow • eqToHom (congrArg (fun i => dual (D.X i))
    (show k + 1 - r = k - (r - 1) by omega)))
  inv := biprod.snd ≫ (r.negOnePow • eqToHom (congrArg (fun i => dual (D.X i))
    (show k - (r - 1) = k + 1 - r by omega)))
  hom_inv_id := by
    simp [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Int.units_mul_self]
  inv_hom_id := by
    apply biprod.hom_ext
    · exact (isZero_zeroX r).eq_of_tgt _ _
    · simp [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Int.units_mul_self]

/-- The isomorphism `ε : C^{k+1-*} ≅ Σ C^{k-*}`. -/
private noncomputable def epsIso (D : ChainComplex B ℤ) (k : ℤ) :
    dualCx D (k + 1) ≅ cone.shift (dualCx D k) :=
  HomologicalComplex.Hom.isoOfComponents (fun r => epsX D k r) (by
    intro i j hij
    simp only [ComplexShape.down_Rel] at hij
    obtain rfl : j = i - 1 := by omega
    change _ ≫ cone.d _ i (i - 1) = _
    simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id]
    apply biprod.hom_ext
    · exact (isZero_zeroX (i - 1)).eq_of_tgt _ _
    · simp only [epsX, Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc,
        Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
      rw [eqToHom_dualHom_d D (a := k + 1 - (i - 1)) (a' := k - (i - 1 - 1)) (b := k + 1 - i)
        (b' := k - (i - 1)) (by omega) (by omega),
        mul_comm])

private lemma epsIso_hom_f (D : ChainComplex B ℤ) (k r : ℤ) :
    (epsIso D k).hom.f r = (epsX D k r).hom :=
  rfl

end Cylinder

open Cylinder in
/-- The cylinder pair `((h, 1) : C ⊞ C' ⟶ C', (χ + Tχ)/2, φ ⊕ (-φ'))` of a homotopy isometry
is a strict `(k+1)`-dimensional Poincaré pair with chain objects in `P`. -/
theorem cylinder_cobordism (P : ObjectProperty B)
    (hsum : ∀ (X Y : B) (c : BinaryBicone X Y), c.IsBilimit → P X → P Y → P c.pt)
    {k : ℤ} (x y : SymPoincare B k)
    (hx : ∀ r, P (x.C.X r)) (hy : ∀ r, P (y.C.X r)) (h : HomotopyEquiv x.C y.C)
    (χ : (StructureCx y.C).X (k + 1))
    (hχ : (StructureCx y.C).d (k + 1) k χ = (StructureCx.push h.hom).f k x.φ - y.φ) :
    ∃ W : SymPair B k (k + 1),
      W.data = ⟨x.C ⊞ y.C, y.C, biprod.desc h.hom (𝟙 y.C),
        (1 / 2 : ℚ) • (χ + (StructureCx.T y.C).f (k + 1) χ), StructureCx.sum x.φ (-y.φ)⟩ ∧
      ∀ r, P (W.C.X r) ∧ P (W.D.X r) := by
  obtain ⟨⟨zC, zφ, zbounded, zcycle, zsymmetric, zpoincare⟩, hz⟩ := SymPoincare.exists_sum x y.neg
  obtain ⟨rfl, hz⟩ := Sigma.mk.inj_iff.mp hz
  obtain rfl := eq_of_heq hz
  have hTT : ∀ (n : ℤ) (a : (StructureCx y.C).X n),
      (StructureCx.T y.C).f n ((StructureCx.T y.C).f n a) = a := fun n a => by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, StructureCx.T_sq]
    rfl
  have hdT : ∀ a : (StructureCx y.C).X (k + 1),
      (StructureCx y.C).d (k + 1) k ((StructureCx.T y.C).f (k + 1) a) =
        (StructureCx.T y.C).f k ((StructureCx y.C).d (k + 1) k a) := fun a => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      HomologicalComplex.Hom.comm]
  have hrel : (StructureCx y.C).d (k + 1) k
      ((1 / 2 : ℚ) • (χ + (StructureCx.T y.C).f (k + 1) χ)) =
      (StructureCx.push (biprod.desc h.hom (𝟙 y.C))).f k (StructureCx.sum x.φ (-y.φ)) := by
    rw [map_smul, map_add, hdT, hχ, map_sub, StructureCx.T_push_apply, x.symmetric,
      y.symmetric, StructureCx.sum, map_add, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      ← StructureCx.push_comp, ← StructureCx.push_comp, biprod.inl_desc, biprod.inr_desc,
      StructureCx.push_id, map_neg]
    simp only [HomologicalComplex.id_f]
    rw [← two_smul ℚ, smul_smul]
    norm_num
    abel
  refine ⟨
    { C := x.C ⊞ y.C
      D := y.C
      f := biprod.desc h.hom (𝟙 y.C)
      δφ := (1 / 2 : ℚ) • (χ + (StructureCx.T y.C).f (k + 1) χ)
      φ := StructureCx.sum x.φ (-y.φ)
      dim := rfl
      boundary_bounded := zbounded
      boundary_cycle := zcycle
      boundary_symmetric := zsymmetric
      boundary_poincare := zpoincare
      bounded := fun r hr => y.bounded r (by omega)
      symmetric := by
        rw [map_smul, map_add, hTT (k + 1) χ]; exact congrArg _ (add_comm _ _)
      rel := hrel
      poincare := ?_ }, rfl, fun r => ⟨hsum _ _ _ (bicone_isBilimit r) (hx r) (hy r), hy r⟩⟩
  obtain ⟨ex, hex⟩ := x.poincare
  have hφq : ∀ (r q q' : ℤ) (e : q = q') (hq : r - 1 + q = k) (hq' : r - 1 + q' = k),
      eqToHom (congrArg (fun i => dual (y.C.X i)) e) ≫ dualHom (h.hom.f q') ≫
        x.φ ⟨(r - 1, q'), hq'⟩ = dualHom (h.hom.f q) ≫ x.φ ⟨(r - 1, q), hq⟩ := by
    rintro r q q' rfl hq hq'
    simp
  let E := ((HomotopyEquiv.ofIso (epsIso y.C k)).trans (cone.shift_homotopyEquiv
    ((dualCx.mapHomotopyEquiv h k).trans ex))).trans (projEquiv h.hom)
  refine ⟨ofHomotopic E _ ((Homotopy.ofEq ?_).trans
    (((projSect h.hom).symm.compLeft _).trans (Homotopy.ofEq (Category.comp_id _)))), rfl⟩
  change ((epsIso y.C k).hom ≫ cone.shiftMap (dualCx.map h.hom k ≫ ex.hom)) ≫ sect h.hom = _
  rw [← Category.assoc]
  congr 1
  rw [hex]
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · exact (isZero_zeroX r).eq_of_tgt _ _
  · simp only [HomologicalComplex.comp_f, Category.assoc, epsIso_hom_f, epsX, cone.shiftMap,
      proj, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
      dualCx.map_f, StructureCx.toHom_f, Linear.units_smul_comp, Linear.comp_units_smul]
    rw [hφq r (k + 1 - r) (k - (r - 1)) (by omega) (by omega) (by omega)]
    congr 1
    rw [StructureCx.sum, Pi.add_apply, StructureCx.push_apply, StructureCx.push_apply]
    simp only [Preadditive.add_comp, Category.assoc, inl_fst_f, inr_fst_f,
      Category.comp_id, comp_zero, add_zero]
    rw [← Category.assoc, ← dualHom_comp, inl_desc_f]

end HSP
