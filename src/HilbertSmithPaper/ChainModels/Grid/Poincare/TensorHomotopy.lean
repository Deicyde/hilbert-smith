import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHomComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorDifferential
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomAddLeft
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomAddRight
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomId

/-!
# Tensor product of homotopies

If `f - 1 = dh + hd` on `C` and `g - 1 = dk + kd` on `E`, for maps `f`, `g` of degree `0` and `h`,
`k` of degree `1`, then `f ⊗ g - 1 = dH + Hd` on `C ⊗ E` for `H = h ⊗ g + 1 ⊗ k`.

## Proof

Write the differential of `C ⊗ E` as `d ⊗ 1 + 1 ⊗ d` and expand `dH + Hd` with the composition
rule for tensors: `d(h ⊗ g) + (h ⊗ g)d = (dh + hd) ⊗ g + h ⊗ (gd - dg)` and
`d(1 ⊗ k) + (1 ⊗ k)d = 1 ⊗ (dk + kd)`, the cross terms cancelling by the Koszul sign. Here
`gd = dg`, since `(g - 1)d = dkd = d(g - 1)`. So `dH + Hd = (f - 1) ⊗ g + 1 ⊗ (g - 1) = f ⊗ g - 1`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP.ChainModels

open FreeQ DualCat

variable {C E : ChainComplex FreeQ ℤ}

/-- Composite of two transported tensors, with the factors of the result given pointwise. -/
private lemma tcomp (hC : ∀ q < 0, (C.X q).dim = 0) (hE : ∀ q < 0, (E.X q).dim = 0)
    (d e d' e' dd ee : ℤ) (hd : d + d' = dd) (he : e + e' = ee)
    (f : ∀ r, C.X r ⟶ C.X (r + d)) (g : ∀ r, E.X r ⟶ E.X (r + e))
    (f' : ∀ r, C.X r ⟶ C.X (r + d')) (g' : ∀ r, E.X r ⟶ E.X (r + e'))
    (F : ∀ a, C.X a ⟶ C.X (a + dd)) (G : ∀ c, E.X c ⟶ E.X (c + ee))
    (hF : ∀ a, f a ≫ f' (a + d) ≫ eqToHom (congrArg C.X (by omega)) = F a)
    (hG : ∀ c, g c ≫ g' (c + e) ≫ eqToHom (congrArg E.X (by omega)) = G c)
    (r s t : ℤ) (h1 : r + (d + e) = s) (h2 : s + (d' + e') = t) :
    basedTensorHom hE hE d e f g r ≫ eqToHom (congrArg (basedComplexTensor C E hE).X h1) ≫
      basedTensorHom hE hE d' e' f' g' s ≫ eqToHom (congrArg (basedComplexTensor C E hE).X h2) =
    (e' * d).negOnePow • (basedTensorHom hE hE dd ee F G r ≫
      eqToHom (congrArg (basedComplexTensor C E hE).X (show r + (dd + ee) = t by omega))) := by
  subst h1 hd he
  obtain rfl : F = _ := funext fun a => (hF a).symm
  obtain rfl : G = _ := funext fun c => (hG c).symm
  rw [eqToHom_refl, Category.id_comp, ← Category.assoc,
    basedTensorHom_comp hE hE hE hC d e d' e' f g f' g' r, Linear.units_smul_comp, Category.assoc,
    eqToHom_trans]

/-- `d_{ij}` followed by a transport is `d_{ij'}`. -/
private lemma d_eqToHom (K : ChainComplex FreeQ ℤ) (i : ℤ) {j j' : ℤ} (h : j = j') :
    K.d i j ≫ eqToHom (congrArg K.X h) = K.d i j' := by
  subst h; simp

/-- A transport followed by `d_{jk}` is `d_{ik}`. -/
private lemma eqToHom_d (K : ChainComplex FreeQ ℤ) {i j : ℤ} (h : i = j) (k : ℤ) :
    eqToHom (congrArg K.X h) ≫ K.d j k = K.d i k := by
  subst h; simp

/-- Transport of a family along an equality of indices. -/
private lemma fam_eqToHom (K : ChainComplex FreeQ ℤ) {c : ℤ} (h : ∀ a, K.X a ⟶ K.X (a + c))
    {a b : ℤ} (e : a = b) {Z : ℤ} (e1 : b + c = Z) (e2 : a + c = Z) :
    eqToHom (congrArg K.X e) ≫ h b ≫ eqToHom (congrArg K.X e1) = h a ≫
        eqToHom (congrArg K.X e2) := by
  subst e; simp

/-- `d_{ij}` followed by a family, reindexed along `j = j'`. -/
private lemma d_fam (K : ChainComplex FreeQ ℤ) {c : ℤ} (h : ∀ a, K.X a ⟶ K.X (a + c)) (i : ℤ)
    {j j' : ℤ} (hj : j = j') {Z : ℤ} (e : j + c = Z) (e' : j' + c = Z) :
    K.d i j ≫ h j ≫ eqToHom (congrArg K.X e) = K.d i j' ≫ h j' ≫ eqToHom (congrArg K.X e') := by
  subst hj; rfl

/-- The `h`-part of the tensor product of homotopies: `d(h ⊗ g) + (h ⊗ g)d = (dh + hd) ⊗ g` for a
chain map `g` of degree `0`. -/
private lemma homotopy_left (hC : ∀ q < 0, (C.X q).dim = 0) (hE : ∀ q < 0, (E.X q).dim = 0)
    (h : ∀ r, C.X r ⟶ C.X (r + 1)) (g : ∀ r, E.X r ⟶ E.X (r + 0))
    (hgd : ∀ c, g c ≫ E.d (c + 0) (c + -1) =
      E.d c (c + -1) ≫ g (c + -1) ≫ eqToHom (congrArg E.X (add_zero (c + -1))))
    (F : ∀ a, C.X a ⟶ C.X (a + 0))
    (hF : ∀ a, F a = (h a ≫ C.d (a + 1) a + C.d a (a - 1) ≫ h (a - 1) ≫
        eqToHom (congrArg C.X (by ring))) ≫ eqToHom (congrArg C.X (add_zero a).symm)) (r : ℤ) :
    (basedTensorHom hE hE 1 0 h g r ≫ eqToHom (congrArg (basedComplexTensor C E hE).X
        (show r + (1 + 0) = r + 1 by ring))) ≫ (basedComplexTensor C E hE).d (r + 1) r +
      (basedComplexTensor C E hE).d r (r - 1) ≫ (basedTensorHom hE hE 1 0 h g (r - 1) ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (show r - 1 + (1 + 0) =
            r - 1 + 1 by ring))) ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (show r - 1 + 1 = r by ring)) =
    basedTensorHom hE hE 0 0 F g r ≫
      eqToHom (congrArg (basedComplexTensor C E hE).X (show r + (0 + 0) = r by ring)) := by
  rw [← d_eqToHom _ (r + 1) (show r + 1 - 1 = r by ring), basedComplexTensor_d_eq hE (r + 1),
    basedComplexTensor_d_eq hE r]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, eqToHom_trans]
  have hA1F : ∀ a, h a ≫ C.d (a + 1) (a + 1 + -1) ≫
      eqToHom (congrArg C.X (show a + 1 + -1 = a + 0 by ring)) =
      (h a ≫ C.d (a + 1) a) ≫ eqToHom (congrArg C.X (add_zero a).symm) := fun a => by
    rw [Category.assoc, ← d_eqToHom C (a + 1) (show a + 1 + -1 = a by ring), Category.assoc,
        eqToHom_trans]
  have hA1G : ∀ c, g c ≫ idDeg0 E (c + 0) ≫
      eqToHom (congrArg E.X (show c + 0 + 0 = c + 0 by ring)) = g c :=
    fun c => by simp [idDeg0]
  let FA1 : ∀ a, C.X a ⟶ C.X (a + 0) := fun a =>
    (h a ≫ C.d (a + 1) a) ≫ eqToHom (congrArg C.X (add_zero a).symm)
  let FB1 : ∀ a, C.X a ⟶ C.X (a + 0) := fun a =>
    (C.d a (a - 1) ≫ h (a - 1) ≫ eqToHom (congrArg C.X (show a - 1 + 1 = a by ring))) ≫
      eqToHom (congrArg C.X (add_zero a).symm)
  have hA2F : ∀ a, h a ≫ idDeg0 C (a + 1) ≫
      eqToHom (congrArg C.X (show a + 1 + 0 = a + 1 by ring)) =
      h a := fun a => by simp [idDeg0]
  have hA2G : ∀ c, g c ≫ E.d (c + 0) (c + 0 + -1) ≫
      eqToHom (congrArg E.X (show c + 0 + -1 = c + -1 by ring)) = g c ≫ E.d (c + 0) (c + -1) :=
    fun c => by rw [d_eqToHom _ _ (show c + 0 + -1 = c + -1 by ring)]
  have hB1F : ∀ a, C.d a (a + -1) ≫ h (a + -1) ≫
      eqToHom (congrArg C.X (show a + -1 + 1 = a + 0 by ring)) = FB1 a := fun a => by
    rw [d_fam C h a (show a + -1 = a - 1 by ring) (show a + -1 + 1 = a + 0 by ring)
      (show a - 1 + 1 = a + 0 by ring)]
    simp only [FB1, Category.assoc, eqToHom_trans]
  have hB1G : ∀ c, idDeg0 E c ≫ g (c + 0) ≫
      eqToHom (congrArg E.X (show c + 0 + 0 = c + 0 by ring)) =
      g c := fun c => by
    simp only [idDeg0]
    rw [fam_eqToHom E g (add_zero c).symm (show c + 0 + 0 = c + 0 by ring) rfl]
    simp
  have hB3F : ∀ a, idDeg0 C a ≫ h (a + 0) ≫
      eqToHom (congrArg C.X (show a + 0 + 1 = a + 1 by ring)) =
      h a := fun a => by
    simp only [idDeg0]
    rw [fam_eqToHom C h (add_zero a).symm (show a + 0 + 1 = a + 1 by ring) rfl]
    simp
  rw [tcomp hC hE 1 0 (-1) 0 0 0 (by norm_num) (by norm_num) h g (fun t => C.d t (t +
      -1)) (idDeg0 E)
      FA1 g hA1F hA1G r (r + 1) r (by ring) (by ring),
    tcomp hC hE 1 0 0 (-1) 1 (-1) (by norm_num) (by norm_num) h g (idDeg0 C) (fun t => E.d t (t +
        -1))
      h _ hA2F hA2G r (r + 1) r (by ring) (by ring),
    tcomp hC hE (-1) 0 1 0 0 0 (by norm_num) (by norm_num) (fun t => C.d t (t + -1)) (idDeg0 E) h g
      FB1 g hB1F hB1G r (r - 1) r (by ring) (by ring),
    tcomp hC hE 0 (-1) 1 0 1 (-1) (by norm_num) (by norm_num) (idDeg0 C) (fun t => E.d t (t +
        -1)) h g
      h _ hB3F (fun c => rfl) r (r - 1) r (by ring) (by ring)]
  simp only [hgd, mul_zero, mul_one, Int.negOnePow_zero, one_smul, mul_neg, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul]
  have key : basedTensorHom hE hE 0 0 F g r =
      basedTensorHom hE hE 0 0 FA1 g r + basedTensorHom hE hE 0 0 FB1 g r := by
    rw [← basedTensorHom_add_left]
    congr 1
    funext a
    rw [hF a]
    simp only [FA1, FB1, Pi.add_apply, Preadditive.add_comp, Category.assoc]
  rw [key, Preadditive.add_comp]
  abel

/-- The `k`-part of the tensor product of homotopies: `d(1 ⊗ k) + (1 ⊗ k)d = 1 ⊗ (dk + kd)`. -/
private lemma homotopy_right (hC : ∀ q < 0, (C.X q).dim = 0) (hE : ∀ q < 0, (E.X q).dim = 0)
    (k : ∀ r, E.X r ⟶ E.X (r + 1)) (G : ∀ c, E.X c ⟶ E.X (c + 0))
    (hG : ∀ c, G c = (k c ≫ E.d (c + 1) c + E.d c (c - 1) ≫ k (c - 1) ≫
        eqToHom (congrArg E.X (by ring))) ≫ eqToHom (congrArg E.X (add_zero c).symm)) (r : ℤ) :
    (basedTensorHom hE hE 0 1 (idDeg0 C) k r ≫ eqToHom (congrArg (basedComplexTensor C E hE).X
        (show r + (0 + 1) = r + 1 by ring))) ≫ (basedComplexTensor C E hE).d (r + 1) r +
      (basedComplexTensor C E hE).d r (r - 1) ≫ (basedTensorHom hE hE 0 1 (idDeg0 C) k (r - 1) ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (show r - 1 + (0 + 1) =
            r - 1 + 1 by ring))) ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (show r - 1 + 1 = r by ring)) =
    basedTensorHom hE hE 0 0 (idDeg0 C) G r ≫
      eqToHom (congrArg (basedComplexTensor C E hE).X (show r + (0 + 0) = r by ring)) := by
  rw [← d_eqToHom _ (r + 1) (show r + 1 - 1 = r by ring), basedComplexTensor_d_eq hE (r + 1),
    basedComplexTensor_d_eq hE r]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, eqToHom_trans]
  let GA4 : ∀ c, E.X c ⟶ E.X (c + 0) := fun c =>
    (k c ≫ E.d (c + 1) c) ≫ eqToHom (congrArg E.X (add_zero c).symm)
  let GB4 : ∀ c, E.X c ⟶ E.X (c + 0) := fun c =>
    (E.d c (c - 1) ≫ k (c - 1) ≫ eqToHom (congrArg E.X (show c - 1 + 1 = c by ring))) ≫
      eqToHom (congrArg E.X (add_zero c).symm)
  have hA3F : ∀ a, idDeg0 C a ≫ C.d (a + 0) (a + 0 + -1) ≫
      eqToHom (congrArg C.X (show a + 0 + -1 = a + -1 by ring)) = C.d a (a + -1) := fun a => by
    simp only [idDeg0]
    rw [d_eqToHom _ _ (show a + 0 + -1 = a + -1 by ring), eqToHom_d C (add_zero a).symm (a + -1)]
  have hA3G : ∀ c, k c ≫ idDeg0 E (c + 1) ≫
      eqToHom (congrArg E.X (show c + 1 + 0 = c + 1 by ring)) =
      k c := fun c => by simp [idDeg0]
  have hA4F : ∀ a, idDeg0 C a ≫ idDeg0 C (a + 0) ≫
      eqToHom (congrArg C.X (show a + 0 + 0 = a + 0 by ring)) = idDeg0 C a := fun a => by
    simp [idDeg0]
  have hA4G : ∀ c, k c ≫ E.d (c + 1) (c + 1 + -1) ≫
      eqToHom (congrArg E.X (show c + 1 + -1 = c + 0 by ring)) = GA4 c := fun c => by
    simp only [GA4]
    rw [Category.assoc, ← d_eqToHom E (c + 1) (show c + 1 + -1 = c by ring), Category.assoc,
        eqToHom_trans]
  have hB2F : ∀ a, C.d a (a + -1) ≫ idDeg0 C (a + -1) ≫
      eqToHom (congrArg C.X (show a + -1 + 0 = a + -1 by ring)) = C.d a (a + -1) := fun a => by
    simp [idDeg0]
  have hB2G : ∀ c, idDeg0 E c ≫ k (c + 0) ≫
      eqToHom (congrArg E.X (show c + 0 + 1 = c + 1 by ring)) =
      k c := fun c => by
    simp only [idDeg0]
    rw [fam_eqToHom E k (add_zero c).symm (show c + 0 + 1 = c + 1 by ring) rfl]
    simp
  have hB4G : ∀ c, E.d c (c + -1) ≫ k (c + -1) ≫
      eqToHom (congrArg E.X (show c + -1 + 1 = c + 0 by ring)) = GB4 c := fun c => by
    rw [d_fam E k c (show c + -1 = c - 1 by ring) (show c + -1 + 1 = c + 0 by ring)
      (show c - 1 + 1 = c + 0 by ring)]
    simp only [GB4, Category.assoc, eqToHom_trans]
  rw [tcomp hC hE 0 1 (-1) 0 (-1) 1 (by norm_num) (by norm_num) (idDeg0 C) k (fun t => C.d t (t +
      -1))
      (idDeg0 E) _ k hA3F hA3G r (r + 1) r (by ring) (by ring),
    tcomp hC hE 0 1 0 (-1) 0 0 (by norm_num) (by norm_num) (idDeg0 C) k (idDeg0 C)
      (fun t => E.d t (t + -1)) (idDeg0 C) GA4 hA4F hA4G r (r + 1) r (by ring) (by ring),
    tcomp hC hE (-1) 0 0 1 (-1) 1 (by norm_num) (by norm_num) (fun t => C.d t (t + -1)) (idDeg0 E)
      (idDeg0 C) k _ k hB2F hB2G r (r - 1) r (by ring) (by ring),
    tcomp hC hE 0 (-1) 0 1 0 0 (by norm_num) (by norm_num) (idDeg0 C) (fun t => E.d t (t + -1))
      (idDeg0 C) k (idDeg0 C) GB4 hA4F hB4G r (r - 1) r (by ring) (by ring)]
  simp only [mul_zero, mul_one, Int.negOnePow_zero, one_smul, mul_neg, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul]
  have key : basedTensorHom hE hE 0 0 (idDeg0 C) G r =
      basedTensorHom hE hE 0 0 (idDeg0 C) GA4 r + basedTensorHom hE hE 0 0 (idDeg0 C) GB4 r := by
    rw [← basedTensorHom_add_right]
    congr 1
    funext c
    rw [hG c]
    simp only [GA4, GB4, Pi.add_apply, Preadditive.add_comp, Category.assoc]
  rw [key, Preadditive.add_comp]
  abel

/-- A map of degree `0` with `g - 1 = dk + kd` commutes with `d`. -/
private lemma chain_of_homotopy (K : ChainComplex FreeQ ℤ) (g : ∀ r, K.X r ⟶ K.X (r + 0))
    (k : ∀ r, K.X r ⟶ K.X (r + 1))
    (hg : ∀ r, g r ≫ eqToHom (congrArg K.X (add_zero r)) - 𝟙 _ =
      k r ≫ K.d (r + 1) r + K.d r (r - 1) ≫ k (r - 1) ≫ eqToHom (congrArg K.X (by ring))) (c : ℤ) :
    g c ≫ K.d (c + 0) (c + -1) =
      K.d c (c + -1) ≫ g (c + -1) ≫ eqToHom (congrArg K.X (add_zero (c + -1))) := by
  suffices aux : ∀ i, i + 1 = c → g c ≫ K.d (c + 0) i =
      K.d c i ≫ g i ≫ eqToHom (congrArg K.X (add_zero i)) from aux _ (by ring)
  intro i hi
  subst hi
  have h1 := hg (i + 1)
  have h2 := hg i
  have aux2 : ∀ a b, a = b → K.d (i + 1) a ≫ k a ≫ K.d (a + 1) i = K.d (i + 1) b ≫ k b ≫
      K.d (b + 1) i := by
    intro a b hab; subst hab; rfl
  rw [← eqToHom_d K (add_zero (i + 1)) i, ← Category.assoc,
    show g (i + 1) ≫ eqToHom (congrArg K.X (add_zero (i + 1))) =
      (g (i + 1) ≫ eqToHom (congrArg K.X (add_zero (i + 1))) - 𝟙 _) + 𝟙 _ by abel, h1,
    show g i ≫ eqToHom (congrArg K.X (add_zero i)) = (g i ≫
        eqToHom (congrArg K.X (add_zero i)) - 𝟙 _) + 𝟙 _
      by abel, h2]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      HomologicalComplex.d_comp_d,
    HomologicalComplex.d_comp_d_assoc, comp_zero, zero_comp, Category.id_comp, Category.comp_id,
        zero_add,
    add_zero]
  rw [eqToHom_d K (show i + 1 - 1 + 1 = i + 1 by ring) i, aux2 _ _ (show i + 1 - 1 = i by ring)]

/-- *Tensor product of homotopies*: if `f - 1 = dh + hd` on `C` and `g - 1 = dk + kd` on `E`, for
maps `f`, `g` of degree `0` and `h`, `k` of degree `1`, then `f ⊗ g - 1 = dH + Hd` on `C ⊗ E` for
`H = h ⊗ g + 1 ⊗ k`. -/
theorem basedTensorHom_homotopy (hC : ∀ q < 0, (C.X q).dim = 0) (hE : ∀ q < 0, (E.X q).dim = 0)
    (f : ∀ r, C.X r ⟶ C.X (r + 0)) (g : ∀ r, E.X r ⟶ E.X (r + 0))
    (h : ∀ r, C.X r ⟶ C.X (r + 1)) (k : ∀ r, E.X r ⟶ E.X (r + 1))
    (hf : ∀ r, f r ≫ eqToHom (congrArg C.X (add_zero r)) - 𝟙 _ =
      h r ≫ C.d (r + 1) r + C.d r (r - 1) ≫ h (r - 1) ≫ eqToHom (congrArg C.X (by ring)))
    (hg : ∀ r, g r ≫ eqToHom (congrArg E.X (add_zero r)) - 𝟙 _ =
      k r ≫ E.d (r + 1) r + E.d r (r - 1) ≫ k (r - 1) ≫ eqToHom (congrArg E.X (by ring)))
    (H : ∀ r, (basedComplexTensor C E hE).X r ⟶ (basedComplexTensor C E hE).X (r + 1))
    (hH : ∀ r, H r = basedTensorHom hE hE 1 0 h g r ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (by ring)) +
      basedTensorHom hE hE 0 1 (idDeg0 C) k r ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (by ring))) (r : ℤ) :
    basedTensorHom hE hE 0 0 f g r ≫
        eqToHom (congrArg (basedComplexTensor C E hE).X (show r + (0 + 0) = r by ring)) - 𝟙 _ =
      H r ≫ (basedComplexTensor C E hE).d (r + 1) r +
        (basedComplexTensor C E hE).d r (r - 1) ≫ H (r - 1) ≫
          eqToHom (congrArg (basedComplexTensor C E hE).X (by ring)) := by
  have L := homotopy_left hC hE h g (chain_of_homotopy E g k hg) (fun a => f a - idDeg0 C a)
    (fun a => by
      rw [← hf a, Preadditive.sub_comp, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id,
        Category.id_comp]
      rfl) r
  have R := homotopy_right hC hE k (fun c => g c - idDeg0 E c)
    (fun c => by
      rw [← hg c, Preadditive.sub_comp, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id,
        Category.id_comp]
      rfl) r
  have hsubL : basedTensorHom hE hE 0 0 (fun a => f a - idDeg0 C a) g r =
      basedTensorHom hE hE 0 0 f g r - basedTensorHom hE hE 0 0 (idDeg0 C) g r := by
    rw [eq_sub_iff_add_eq, ← basedTensorHom_add_left]
    congr 1
    funext a
    simp
  have hsubR : basedTensorHom hE hE 0 0 (idDeg0 C) (fun c => g c - idDeg0 E c) r =
      basedTensorHom hE hE 0 0 (idDeg0 C) g r - basedTensorHom hE hE 0 0 (idDeg0 C) (idDeg0 E) r
          := by
    rw [eq_sub_iff_add_eq, ← basedTensorHom_add_right]
    congr 1
    funext c
    simp
  rw [hsubL, Preadditive.sub_comp] at L
  have hid : basedTensorHom hE hE 0 0 (idDeg0 C) (idDeg0 E) r ≫
      eqToHom (congrArg (basedComplexTensor C E hE).X (show r + (0 + 0) = r by ring)) = 𝟙 _ := by
    rw [basedTensorHom_id, eqToHom_trans, eqToHom_refl]
  rw [hsubR, Preadditive.sub_comp, hid] at R
  have rearr : ∀ a b c e : (basedComplexTensor C E hE).X r ⟶ (basedComplexTensor C E hE).X r,
      (a + b) + (c + e) = (a + c) + (b + e) := fun _ _ _ _ => by abel
  rw [hH r, hH (r - 1), Preadditive.add_comp, Preadditive.add_comp, Preadditive.comp_add, rearr,
      L, R]
  abel

end HSP.ChainModels
