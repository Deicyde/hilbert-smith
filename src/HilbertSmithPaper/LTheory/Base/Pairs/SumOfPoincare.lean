import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePushInvolution

/-!
# Sums of Poincaré complexes

If `(C, φ)` and `(C', φ')` are strict `k`-dimensional symmetric Poincaré complexes, then so is
`(C ⊞ C', φ ⊕ φ')`; write `(C, φ) ⊕ (C', φ')` for it (`SymPoincare.sum`). Likewise `(C, -φ)`
(`SymPoincare.neg`) and the zero complex with the zero structure (`SymPoincare.zero`) are strict
`k`-dimensional symmetric Poincaré complexes.

Lean: the statement `SymPoincare.exists_sum` says that some `z : SymPoincare B k` has
`(z.C, z.φ) = (C ⊞ C', φ ⊕ φ')` in the Σ-type of structured complexes; `SymPoincare.sum` chooses
it (it is unique, the remaining fields being propositions).
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace SymPoincare

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

/-- The sum `(C ⊞ C', φ ⊕ φ')` of strict `k`-dimensional symmetric Poincaré complexes is a
strict `k`-dimensional symmetric Poincaré complex. -/
theorem exists_sum {k : ℤ} (x y : SymPoincare B k) :
    ∃ z : SymPoincare B k, (⟨z.C, z.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩ := by
  have hcyc : (StructureCx (x.C ⊞ y.C)).d k (k - 1) (StructureCx.sum x.φ y.φ) = 0 := by
    rw [StructureCx.sum, map_add, StructureCx.d_push_apply, StructureCx.d_push_apply, x.cycle,
      y.cycle, map_zero, map_zero, add_zero]
  refine ⟨
    { C := x.C ⊞ y.C
      φ := StructureCx.sum x.φ y.φ
      bounded := fun r hr => IsZero.of_iso (isZero_biprod (x.bounded r hr) (y.bounded r hr))
        (HomologicalComplex.biprodXIso x.C y.C r)
      cycle := hcyc
      symmetric := by
        rw [StructureCx.sum, map_add, StructureCx.T_push_apply, StructureCx.T_push_apply,
          x.symmetric, y.symmetric]
      poincare := ?_ }, rfl⟩
  obtain ⟨e, he⟩ := x.poincare
  obtain ⟨e', he'⟩ := y.poincare
  refine ⟨(HomotopyEquiv.ofIso (dualBiprodIso x.C y.C k)).trans (biprodHomotopyEquiv e e'), ?_⟩
  change (dualBiprodIso x.C y.C k).hom ≫ biprod.map e.hom e'.hom = _
  rw [he, he']
  apply biprod.hom_ext
  · refine HomologicalComplex.hom_ext _ _ fun r => ?_
    have h1 : (biprod.inl : x.C ⟶ x.C ⊞ y.C).f r ≫ (biprod.fst : x.C ⊞ y.C ⟶ x.C).f r = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
    have h2 : (biprod.inr : y.C ⟶ x.C ⊞ y.C).f r ≫ (biprod.fst : x.C ⊞ y.C ⟶ x.C).f r = 0 := by
      rw [← HomologicalComplex.comp_f, biprod.inr_fst, HomologicalComplex.zero_f]
    simp only [dualBiprodIso, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      HomologicalComplex.comp_f]
    change _ = (StructureCx.sum x.φ y.φ ⟨(r, k - r), _⟩) ≫ _
    simp only [StructureCx.sum, Pi.add_apply, Preadditive.add_comp]
    rw [StructureCx.push_apply, StructureCx.push_apply]
    simp [h1, h2]
  · refine HomologicalComplex.hom_ext _ _ fun r => ?_
    have h1 : (biprod.inr : y.C ⟶ x.C ⊞ y.C).f r ≫ (biprod.snd : x.C ⊞ y.C ⟶ y.C).f r = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
    have h2 : (biprod.inl : x.C ⟶ x.C ⊞ y.C).f r ≫ (biprod.snd : x.C ⊞ y.C ⟶ y.C).f r = 0 := by
      rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
    simp only [dualBiprodIso, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      HomologicalComplex.comp_f]
    change _ = (StructureCx.sum x.φ y.φ ⟨(r, k - r), _⟩) ≫ _
    simp only [StructureCx.sum, Pi.add_apply, Preadditive.add_comp]
    rw [StructureCx.push_apply, StructureCx.push_apply]
    simp [h1, h2]

/-- The sum `(C, φ) ⊕ (C', φ') = (C ⊞ C', φ ⊕ φ')`. -/
noncomputable def sum {k : ℤ} (x y : SymPoincare B k) : SymPoincare B k :=
  (exists_sum x y).choose

lemma sum_spec {k : ℤ} (x y : SymPoincare B k) :
    (⟨(sum x y).C, (sum x y).φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩ :=
  (exists_sum x y).choose_spec

private def negHomotopyEquiv {C D : ChainComplex B ℤ} (e : HomotopyEquiv C D) :
    HomotopyEquiv C D where
  hom := -e.hom
  inv := -e.inv
  homotopyHomInvId := (Homotopy.ofEq (Preadditive.neg_comp_neg _ _)).trans e.homotopyHomInvId
  homotopyInvHomId := (Homotopy.ofEq (Preadditive.neg_comp_neg _ _)).trans e.homotopyInvHomId

/-- The negative `(C, -φ)` of a strict `k`-dimensional symmetric Poincaré complex. -/
@[simps]
def neg {k : ℤ} (x : SymPoincare B k) : SymPoincare B k where
  C := x.C
  φ := -x.φ
  bounded := x.bounded
  cycle := by rw [map_neg, x.cycle, neg_zero]
  symmetric := by rw [map_neg, x.symmetric]
  poincare := by
    obtain ⟨e, he⟩ := x.poincare
    refine ⟨negHomotopyEquiv e, ?_⟩
    ext r
    change -e.hom.f r = -x.φ ⟨(r, k - r), _⟩
    rw [he]
    rfl

open ZeroObject in
/-- The zero complex. -/
private noncomputable def zeroCx : ChainComplex B ℤ where
  X _ := 0
  d _ _ := 0

private lemma isZero_dual {X : B} (hX : IsZero X) : IsZero (dual X) := by
  rw [IsZero.iff_id_eq_zero, ← dualHom_id, (IsZero.iff_id_eq_zero X).mp hX, dualHom_zero]

omit [Linear ℚ B] [DualCat B] in
private lemma isZero_zeroCx (r : ℤ) : IsZero ((zeroCx : ChainComplex B ℤ).X r) := isZero_zero B

/-- The zero complex with the zero structure, a strict `k`-dimensional symmetric Poincaré
complex. -/
noncomputable def zero (k : ℤ) : SymPoincare B k where
  C := zeroCx
  φ := 0
  bounded r _ := isZero_zeroCx r
  cycle := map_zero _
  symmetric := map_zero _
  poincare := by
    refine ⟨HomotopyEquiv.ofIso (HomologicalComplex.Hom.isoOfComponents
      (fun r => IsZero.iso (isZero_dual (isZero_zeroCx (k - r))) (isZero_zeroCx r))
      (fun i _ _ => IsZero.eq_of_src (isZero_dual (isZero_zeroCx (k - i))) _ _)), ?_⟩
    ext r
    exact IsZero.eq_of_src (isZero_dual (isZero_zeroCx (k - r))) _ _

end SymPoincare

end HSP
