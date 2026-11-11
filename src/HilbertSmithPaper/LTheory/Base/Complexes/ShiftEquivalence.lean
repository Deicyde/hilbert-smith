import HilbertSmithPaper.LTheory.Base.Complexes.Cone

/-!
# Shifts of homotopy equivalences

For a chain map `h : C' ⟶ C`, `Σh : ΣC' ⟶ ΣC` is `h_{r-1}` on the summand `C'_{r-1}` of
`(ΣC')_r = 0 ⊞ C'_{r-1}`, with `Σ = cone (· ⟶ 0)` the shift of the mapping cone article. The
differential of `ΣC` is `d` on the summand `C_{r-1}`, with no sign, so `Σ` is functorial and a
homotopy `H` gives the homotopy `(ΣH)_r = H_{r-1}`. Hence `Σ` preserves chain homotopy
equivalences.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open ZeroObject

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V] [HasZeroObject V]

namespace cone

omit [HasBinaryBiproducts V] in
private lemma isZero_zeroX (r : ℤ) : IsZero ((0 : ChainComplex V ℤ).X r) :=
  (HomologicalComplex.eval V _ r).map_isZero (isZero_zero _)

/-- The shift `Σh : ΣC' ⟶ ΣC` of a chain map `h : C' ⟶ C`: `h_{r-1}` on `C'_{r-1}`. -/
noncomputable def shiftMap {C' C : ChainComplex V ℤ} (h : C' ⟶ C) : shift C' ⟶ shift C where
  f r := biprod.map (𝟙 _) (h.f (r - 1))
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    obtain rfl : j = i - 1 := by omega
    change _ ≫ cone.d _ i (i - 1) = cone.d _ i (i - 1) ≫ _
    simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id]
    apply biprod.hom_ext
    · exact (isZero_zeroX (V := V) (i - 1)).eq_of_tgt _ _
    · simp

private lemma shiftMap_comp {C'' C' C : ChainComplex V ℤ} (g : C'' ⟶ C') (h : C' ⟶ C) :
    shiftMap (g ≫ h) = shiftMap g ≫ shiftMap h := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · exact (isZero_zeroX (V := V) r).eq_of_tgt _ _
  · simp [shiftMap]

private lemma shiftMap_id (C : ChainComplex V ℤ) : shiftMap (𝟙 C) = 𝟙 (shift C) := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · exact (isZero_zeroX (V := V) r).eq_of_tgt _ _
  · simp [shiftMap]

private lemma shiftMap_sub {C' C : ChainComplex V ℤ} (f g : C' ⟶ C) :
    shiftMap (f - g) = shiftMap f - shiftMap g := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  apply biprod.hom_ext
  · exact (isZero_zeroX (V := V) r).eq_of_tgt _ _
  · simp [shiftMap]

/-- The shift of a homotopy: `(ΣH)_r = H_{r-1}`. -/
private noncomputable def shiftHomotopy {C' C : ChainComplex V ℤ} {f g : C' ⟶ C}
    (H : Homotopy f g) : Homotopy (shiftMap f) (shiftMap g) := by
  refine Homotopy.equivSubZero.symm ((Homotopy.ofEq ?_).trans (Homotopy.nullHomotopy'
    (fun i j _ => biprod.map (0 : (0 : ChainComplex V ℤ).X i ⟶ (0 : ChainComplex V ℤ).X j)
      (H.hom (i - 1) (j - 1)))))
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  rw [Homotopy.nullHomotopicMap'_f (k₂ := k + 1) (k₀ := k - 1) (by simp) (by simp),
    HomologicalComplex.sub_f_apply]
  have hc := H.comm (k - 1)
  rw [dNext_eq H.hom (i' := k - 1 - 1) (by simp only [ComplexShape.down_Rel]; omega),
    prevD_eq H.hom (j' := k) (by simp only [ComplexShape.down_Rel]; omega)] at hc
  change _ = cone.d (0 : C' ⟶ 0) k (k - 1) ≫ _ + _ ≫ cone.d (0 : C ⟶ 0) (k + 1) k
  have e1 : k + 1 - 1 = k := by omega
  simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, show k + 1 - 1 = k from e1]
  have e2 : ∀ a, a = k → H.hom (k - 1) a ≫ C.d a (k - 1) = H.hom (k - 1) k ≫ C.d k (k - 1) := by
    rintro a rfl; rfl
  apply biprod.hom_ext
  · exact (isZero_zeroX (V := V) k).eq_of_tgt _ _
  · simp [shiftMap, hc, e2 _ e1]

/-- `Σ` preserves chain homotopy equivalences: for `h : C' ⟶ C` a chain homotopy equivalence,
`Σh : ΣC' ⟶ ΣC` is one. -/
noncomputable def shift_homotopyEquiv {C' C : ChainComplex V ℤ} (e : HomotopyEquiv C' C) :
    HomotopyEquiv (shift C') (shift C) where
  hom := shiftMap e.hom
  inv := shiftMap e.inv
  homotopyHomInvId := (Homotopy.ofEq (shiftMap_comp _ _).symm).trans
    ((shiftHomotopy e.homotopyHomInvId).trans (Homotopy.ofEq (shiftMap_id _)))
  homotopyInvHomId := (Homotopy.ofEq (shiftMap_comp _ _).symm).trans
    ((shiftHomotopy e.homotopyInvHomId).trans (Homotopy.ofEq (shiftMap_id _)))

@[simp]
lemma shift_homotopyEquiv_hom {C' C : ChainComplex V ℤ} (e : HomotopyEquiv C' C) :
    (shift_homotopyEquiv e).hom = shiftMap e.hom :=
  rfl

end cone

end HSP
