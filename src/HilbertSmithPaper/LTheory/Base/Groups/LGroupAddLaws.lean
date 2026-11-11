import HilbertSmithPaper.LTheory.Base.Pairs.IsoCobordism
import HilbertSmithPaper.LTheory.Base.Pairs.TransportCobordism
import HilbertSmithPaper.LTheory.Base.Pairs.PoincareSum
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPairs

/-!
# Sum of Poincaré complexes up to cobordism

Up to cobordism, the sum of strict `k`-dimensional symmetric Poincaré complexes is compatible
with cobordism, negation is compatible with cobordism, and the sum is associative and
commutative, with unit `(0, 0)` and inverse `(C, -φ)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

private lemma sigma_of_data {m n : ℤ} (W : SymPair B m n) {C D : ChainComplex B ℤ}
    {f : C ⟶ D} {δφ : (StructureCx D).X n} {φ : (StructureCx C).X m}
    (h : W.data = ⟨C, D, f, δφ, φ⟩) :
    (⟨W.C, W.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X m) = ⟨C, φ⟩ := by
  obtain ⟨C₀, D₀, f₀, δφ₀, φ₀⟩ := W
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h)
  have h' := eq_of_heq h
  simp only [Prod.mk.injEq] at h'
  exact congrArg (Sigma.mk C₀) h'.2.2

namespace StructureCx

private lemma push_comp_apply {C D E : ChainComplex B ℤ} (g : C ⟶ D) (h : D ⟶ E) {k : ℤ}
    (a : (StructureCx C).X k) :
    (push (g ≫ h)).f k a = (push h).f k ((push g).f k a) := by
  rw [push_comp]
  rfl

private lemma push_sum {X Y Z : ChainComplex B ℤ} (g : X ⊞ Y ⟶ Z) {k : ℤ}
    (a : (StructureCx X).X k) (b : (StructureCx Y).X k) :
    (push g).f k (StructureCx.sum a b) = (push (biprod.inl ≫ g)).f k a + (push (biprod.inr ≫ g)).f k b := by
  rw [StructureCx.sum, map_add, push_comp_apply, push_comp_apply]

private lemma push_map_sum {X Y X' Y' : ChainComplex B ℤ} (g : X ⟶ X') (g' : Y ⟶ Y') {k : ℤ}
    (a : (StructureCx X).X k) (b : (StructureCx Y).X k) :
    (push (biprod.map g g')).f k (StructureCx.sum a b) = StructureCx.sum ((push g).f k a) ((push g').f k b) := by
  rw [push_sum, biprod.inl_map, biprod.inr_map, push_comp_apply, push_comp_apply, StructureCx.sum]

private lemma sum_neg {X Y : ChainComplex B ℤ} {k : ℤ} (a : (StructureCx X).X k)
    (b : (StructureCx Y).X k) : StructureCx.sum (-a) (-b) = -StructureCx.sum a b := by
  rw [StructureCx.sum, StructureCx.sum, map_neg, map_neg, neg_add]

private lemma push_inv_hom {C D : ChainComplex B ℤ} (u : C ≅ D) {k : ℤ}
    (a : (StructureCx C).X k) : (push u.inv).f k ((push u.hom).f k a) = a := by
  rw [← push_comp_apply, u.hom_inv_id, push_id]
  rfl

private lemma exists_iso_of_sigma_eq {k : ℤ} {C₀ C : ChainComplex B ℤ} {φ₀ : (StructureCx C₀).X k}
    {φ : (StructureCx C).X k}
    (h : (⟨C₀, φ₀⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) = ⟨C, φ⟩) :
    ∃ u : C ≅ C₀, (push u.hom).f k φ = φ₀ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq h
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, push_id]; rfl⟩

end StructureCx

open StructureCx

namespace AddLaws

open StructureCx

/-- `(P ⊞ Q) ⊞ (R ⊞ S) ≅ (P ⊞ R) ⊞ (Q ⊞ S)`. -/
private noncomputable def shuffle (P Q R S : ChainComplex B ℤ) :
    (P ⊞ Q) ⊞ (R ⊞ S) ≅ (P ⊞ R) ⊞ (Q ⊞ S) where
  hom := biprod.lift (biprod.map biprod.fst biprod.fst) (biprod.map biprod.snd biprod.snd)
  inv := biprod.lift (biprod.map biprod.fst biprod.fst) (biprod.map biprod.snd biprod.snd)
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      apply biprod.hom_ext <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      apply biprod.hom_ext <;> simp

/-- `P ⊞ Q ≅ Q ⊞ P`. -/
private noncomputable def braid (P Q : ChainComplex B ℤ) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

/-- `(P ⊞ Q) ⊞ R ≅ P ⊞ (Q ⊞ R)`. -/
private noncomputable def assoc (P Q R : ChainComplex B ℤ) : (P ⊞ Q) ⊞ R ≅ P ⊞ (Q ⊞ R) where
  hom := biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

private lemma push_assoc {P Q R : ChainComplex B ℤ} {k : ℤ} (a : (StructureCx P).X k)
    (b : (StructureCx Q).X k) (c : (StructureCx R).X k) :
    (push (assoc P Q R).hom).f k (StructureCx.sum (StructureCx.sum a b) c) = StructureCx.sum a (StructureCx.sum b c) := by
  have e1 : biprod.inl ≫ biprod.inl ≫ (assoc P Q R).hom = biprod.inl := by
    apply biprod.hom_ext
    · simp [assoc]
    · apply biprod.hom_ext <;> simp [assoc]
  have e2 : biprod.inr ≫ biprod.inl ≫ (assoc P Q R).hom = biprod.inl ≫ biprod.inr := by
    apply biprod.hom_ext
    · simp [assoc]
    · apply biprod.hom_ext <;> simp [assoc]
  have e3 : biprod.inr ≫ (assoc P Q R).hom = biprod.inr ≫ biprod.inr := by
    apply biprod.hom_ext
    · simp [assoc]
    · apply biprod.hom_ext <;> simp [assoc]
  rw [push_sum, push_sum, e1, e2, e3, StructureCx.sum, StructureCx.sum, map_add,
    push_comp_apply biprod.inl biprod.inr b, push_comp_apply biprod.inr biprod.inr c]
  abel

private lemma push_shuffle {P Q R S : ChainComplex B ℤ} {k : ℤ} (a : (StructureCx P).X k)
    (b : (StructureCx Q).X k) (c : (StructureCx R).X k) (d : (StructureCx S).X k) :
    (push (shuffle P Q R S).hom).f k (StructureCx.sum (StructureCx.sum a b) (StructureCx.sum c d)) = StructureCx.sum (StructureCx.sum a c) (StructureCx.sum b d) := by
  have e1 : biprod.inl ≫ biprod.inl ≫ (shuffle P Q R S).hom = biprod.inl ≫ biprod.inl := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [shuffle]
  have e2 : biprod.inr ≫ biprod.inl ≫ (shuffle P Q R S).hom = biprod.inl ≫ biprod.inr := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [shuffle]
  have e3 : biprod.inl ≫ biprod.inr ≫ (shuffle P Q R S).hom = biprod.inr ≫ biprod.inl := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [shuffle]
  have e4 : biprod.inr ≫ biprod.inr ≫ (shuffle P Q R S).hom = biprod.inr ≫ biprod.inr := by
    apply biprod.hom_ext <;> apply biprod.hom_ext <;> simp [shuffle]
  rw [push_sum, push_sum, push_sum, e1, e2, e3, e4, StructureCx.sum, StructureCx.sum,
    StructureCx.sum, map_add, map_add,
    push_comp_apply, push_comp_apply, push_comp_apply, push_comp_apply]
  abel

end AddLaws

open AddLaws StructureCx in
/-- The laws of the sum of strict symmetric Poincaré complexes up to cobordism. -/
theorem cobordant_sum_laws {k : ℤ} :
    (∀ x x' y y' : SymPoincare B k, Cobordant x x' → Cobordant y y' →
      Cobordant (x.sum y) (x'.sum y')) ∧
    (∀ x y : SymPoincare B k, Cobordant x y → Cobordant x.neg y.neg) ∧
    (∀ x y z : SymPoincare B k, Cobordant ((x.sum y).sum z) (x.sum (y.sum z))) ∧
    (∀ x y : SymPoincare B k, Cobordant (x.sum y) (y.sum x)) ∧
    (∀ x : SymPoincare B k, Cobordant ((SymPoincare.zero k).sum x) x) ∧
    (∀ x : SymPoincare B k, Cobordant (x.neg.sum x) (SymPoincare.zero k)) := by
  have hZ : IsZero (SymPoincare.zero (B := B) k).C := by
    rw [IsZero.iff_id_eq_zero]
    ext r
    exact (isZero_zero B).eq_of_src _ _
  have hz0 : (SymPoincare.zero (B := B) k).φ = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x x' y y' ⟨W₁, h₁⟩ ⟨W₂, h₂⟩
    obtain ⟨u₁, hu₁⟩ := exists_iso_of_sigma_eq h₁
    obtain ⟨u₂, hu₂⟩ := exists_iso_of_sigma_eq h₂
    obtain ⟨W, hW⟩ := SymPair.sum W₁ W₂
    obtain ⟨u, hu⟩ := exists_iso_of_sigma_eq (sigma_of_data W hW)
    obtain ⟨s, hs⟩ := SymPoincare.exists_sum_iso x y
    obtain ⟨s', hs'⟩ := SymPoincare.exists_sum_iso x' y'
    refine Cobordant.of_transport _ _ W (biprod.mapIso s.symm s'.symm ≪≫ shuffle _ _ _ _ ≪≫
      biprod.mapIso u₁ u₂ ≪≫ u) _ ?_ 1 (one_smul _ _)
    simp only [Iso.trans_hom, biprod.mapIso_hom, Iso.symm_hom]
    rw [push_comp_apply, push_comp_apply, push_comp_apply, push_map_sum, ← hs, ← hs', map_neg, push_inv_hom, push_inv_hom, ← sum_neg,
      push_shuffle, push_map_sum, hu₁, hu₂, hu]
  · rintro x y ⟨W, h⟩
    obtain ⟨u, hu⟩ := exists_iso_of_sigma_eq h
    refine Cobordant.of_transport x.neg y.neg W u _ hu (-1) ?_
    change (-1 : ℤˣ) • StructureCx.sum x.φ (-y.φ) = StructureCx.sum (-x.φ) (-(-y.φ))
    rw [sum_neg, Units.neg_smul, one_smul]
  · intro x y z
    obtain ⟨s₁, hs₁⟩ := SymPoincare.exists_sum_iso x y
    obtain ⟨s₂, hs₂⟩ := SymPoincare.exists_sum_iso (x.sum y) z
    obtain ⟨s₃, hs₃⟩ := SymPoincare.exists_sum_iso y z
    obtain ⟨s₄, hs₄⟩ := SymPoincare.exists_sum_iso x (y.sum z)
    refine Cobordant.of_iso _ _ (s₂.symm ≪≫ biprod.mapIso s₁.symm (Iso.refl _) ≪≫
      assoc _ _ _ ≪≫ biprod.mapIso (Iso.refl _) s₃ ≪≫ s₄) ?_
    simp only [Iso.trans_hom, biprod.mapIso_hom, Iso.symm_hom, Iso.refl_hom]
    rw [push_comp_apply, push_comp_apply, push_comp_apply, push_comp_apply, ← hs₂,
      push_inv_hom, push_map_sum, ← hs₁, push_inv_hom, push_id]
    change (push s₄.hom).f k ((push (biprod.map (𝟙 x.C) s₃.hom)).f k
      ((push (assoc x.C y.C z.C).hom).f k (StructureCx.sum (StructureCx.sum x.φ y.φ) z.φ))) = _
    rw [push_assoc, push_map_sum, hs₃, push_id]
    change (push s₄.hom).f k (StructureCx.sum x.φ (y.sum z).φ) = _
    rw [hs₄]
  · intro x y
    obtain ⟨s₁, hs₁⟩ := SymPoincare.exists_sum_iso x y
    obtain ⟨s₂, hs₂⟩ := SymPoincare.exists_sum_iso y x
    refine Cobordant.of_iso _ _ (s₁.symm ≪≫ braid _ _ ≪≫ s₂) ?_
    simp only [Iso.trans_hom, Iso.symm_hom]
    have e1 : biprod.inl ≫ (braid x.C y.C).hom = biprod.inr := by
      apply biprod.hom_ext <;> simp [braid]
    have e2 : biprod.inr ≫ (braid x.C y.C).hom = biprod.inl := by
      apply biprod.hom_ext <;> simp [braid]
    rw [push_comp_apply, push_comp_apply, ← hs₁, push_inv_hom, ← hs₂, push_sum, e1, e2]
    exact congrArg _ (add_comm _ _)
  · intro x
    obtain ⟨s, hs⟩ := SymPoincare.exists_sum_iso (SymPoincare.zero k) x
    refine Cobordant.of_iso _ _ (s.symm ≪≫ (isoZeroBiprod hZ).symm) ?_
    simp only [Iso.trans_hom, Iso.symm_hom]
    have e : biprod.inr ≫ (isoZeroBiprod (Y := x.C) hZ).inv = 𝟙 _ := biprod.inr_snd
    rw [push_comp_apply, ← hs, push_inv_hom, push_sum, hz0, map_zero, zero_add, e, push_id]
    rfl
  · intro x
    obtain ⟨W, hW, -⟩ := cylinder_cobordism ⊤ (fun _ _ _ _ _ _ => trivial) x x
      (fun _ => trivial) (fun _ => trivial) (HomotopyEquiv.refl x.C) 0
      (by
        rw [map_zero]
        change 0 = (push (𝟙 x.C)).f k x.φ - x.φ
        rw [push_id]
        exact (sub_self _).symm)
    obtain ⟨u, hu⟩ : ∃ u : x.neg.C ⊞ x.C ≅ W.C,
        (push u.hom).f k (StructureCx.sum x.φ (-x.φ)) = W.φ :=
      exists_iso_of_sigma_eq (sigma_of_data W hW)
    obtain ⟨s, hs⟩ := SymPoincare.exists_sum_iso x.neg x
    refine Cobordant.of_transport _ _ W ((isoBiprodZero hZ).symm ≪≫ s.symm ≪≫ u)
      (-StructureCx.sum (x.neg.sum x).φ (-(SymPoincare.zero k).φ)) ?_ (-1)
      (by rw [Units.neg_smul, one_smul, neg_neg])
    simp only [Iso.trans_hom, Iso.symm_hom]
    have e : biprod.inl ≫ (isoBiprodZero (X := (x.neg.sum x).C) hZ).inv = 𝟙 _ :=
      biprod.inl_fst
    rw [push_comp_apply, push_comp_apply, map_neg, push_sum, hz0, neg_zero, map_zero, add_zero,
      e, push_id]
    change (push u.hom).f k ((push s.inv).f k (-(x.neg.sum x).φ)) = W.φ
    rw [← hs, map_neg, push_inv_hom]
    change (push u.hom).f k (-StructureCx.sum (-x.φ) x.φ) = W.φ
    rw [← sum_neg, neg_neg]
    exact hu

end HSP
