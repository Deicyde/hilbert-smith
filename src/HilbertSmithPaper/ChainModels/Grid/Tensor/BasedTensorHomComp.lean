import Mathlib
import HilbertSmithPaper.ChainModels.Grid.Tensor.BasedTensorHom
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockExt
import HilbertSmithPaper.ChainModels.Grid.Tensor.BlockComp
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronComposite
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronTransport
import HilbertSmithPaper.ChainModels.Grid.Tensor.KronZero
import HilbertSmithPaper.ChainModels.Grid.Tensor.TensorHomBlocks

/-!
# Composition of tensors of graded maps

For graded maps `f, g` of degrees `d, e` and `f', g'` of degrees `d', e'`, with the middle complex `C'` and the second factors vanishing in negative degrees, `(f' ⊗ g') ∘ (f ⊗ g) = (-1)^{e' d} (f' f) ⊗ (g' g)`, up to the identity transport of the target degree.

## Proof

Blockwise: the only middle summand is `p + d`; when it is outside the range of summands, the corresponding factor of `C'` or `E'` vanishes, so both sides are zero.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Kronecker

namespace HSP.ChainModels

open FreeQ DualCat

variable {C C' C'' E E' E'' : ChainComplex FreeQ ℤ}

/-- `block_comp` with the objects written as degrees of tensor complexes: the later rewrites
(`blk_smul_eqToHom`, the blocks of `basedTensorHom`) match only this form, not the `⟨∑ i, d i⟩` form
of `block_comp`'s statement. -/
private lemma blk_comp (hE : ∀ q < 0, (E.X q).dim = 0) (hE' : ∀ q < 0, (E'.X q).dim = 0)
    (hE'' : ∀ q < 0, (E''.X q).dim = 0) {r s t : ℤ}
    (F : (basedComplexTensor C E hE).X r ⟶ (basedComplexTensor C' E' hE').X s)
    (G : (basedComplexTensor C' E' hE').X s ⟶ (basedComplexTensor C'' E'' hE'').X t)
    (p : Fin (r.toNat + 1)) (q : Fin (t.toNat + 1)) :
    blockInc (tensorSummandDim C E r) p ≫ (F ≫ G) ≫ blockProj (tensorSummandDim C'' E'' t) q =
      ∑ p', (blockInc (tensorSummandDim C E r) p ≫ F ≫ blockProj (tensorSummandDim C' E' s) p') ≫
        (blockInc (tensorSummandDim C' E' s) p' ≫ G ≫ blockProj (tensorSummandDim C'' E'' t) q) :=
  block_comp F G p q

private lemma comp_units_smul_comp {W X Y Z : FreeQ} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (u : ℤˣ) :
    f ≫ (u • g) ≫ h = u • (f ≫ g ≫ h) := by
  rw [Linear.units_smul_comp, Linear.comp_units_smul]

private lemma blk_smul_eqToHom (hE : ∀ q < 0, (E.X q).dim = 0) (hE' : ∀ q < 0, (E'.X q).dim = 0)
    {r s t : ℤ} (T : (basedComplexTensor C E hE).X r ⟶ (basedComplexTensor C' E' hE').X s)
    (h : s = t) (u : ℤˣ) (p : Fin (r.toNat + 1)) (q : Fin (t.toNat + 1)) :
    blockInc (tensorSummandDim C E r) p ≫
        (u • (T ≫ eqToHom (congrArg (basedComplexTensor C' E' hE').X h))) ≫
      blockProj (tensorSummandDim C' E' t) q =
    u • ((blockInc (tensorSummandDim C E r) p ≫ T ≫
      blockProj (tensorSummandDim C' E' s) (Fin.cast (by rw [h]) q)) ≫ eqToHom (by subst h; rfl)) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact comp_units_smul_comp _ _ _ _

private lemma kron_transport_assoc {A A' B B' : ℤ → FreeQ} (f : ∀ t, A t ⟶ A' t)
    (g : ∀ t, B t ⟶ B' t) {t t' s s' : ℤ} (h1 : t = t') (h2 : s = s')
    (h : (⟨(A t).dim * (B s).dim⟩ : FreeQ) = ⟨(A t').dim * (B s').dim⟩) {Z : FreeQ}
    (k : (⟨(A' t').dim * (B' s').dim⟩ : FreeQ) ⟶ Z) :
    eqToHom h ≫ basedKron (f t') (g s') ≫ k =
      basedKron (f t) (g s) ≫ eqToHom (by subst h1 h2; rfl) ≫ k := by
  subst h1 h2; simp

private lemma kron_split {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : FreeQ} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (a' : Y₀ ⟶ Y₁) (b' : Y₁ ⟶ Y₂) (h : X₂ = X₃) (h' : Y₂ = Y₃) :
    basedKron (a ≫ b ≫ eqToHom h) (a' ≫ b' ≫ eqToHom h') =
      basedKron (a ≫ b) (a' ≫ b') ≫ eqToHom (by rw [h, h']) := by
  rw [← Category.assoc a, ← Category.assoc a', ← basedKron_comp_basedKron, basedKron_eqToHom]

private lemma basedKron_comp_basedKron_assoc {X₀ X₁ X₂ Y₀ Y₁ Y₂ Z : FreeQ}
    (f : X₀ ⟶ X₁) (f' : X₁ ⟶ X₂) (g : Y₀ ⟶ Y₁) (g' : Y₁ ⟶ Y₂)
    (k : (⟨X₂.dim * Y₂.dim⟩ : FreeQ) ⟶ Z) :
    basedKron f g ≫ basedKron f' g' ≫ k = basedKron (f ≫ f') (g ≫ g') ≫ k := by
  rw [← Category.assoc, basedKron_comp_basedKron]

private lemma comp_zero_of_dim {X Y Z : FreeQ} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y.dim = 0) :
    f ≫ g = 0 :=
  Matrix.ext fun i j => by
    change (toMatrix g * toMatrix f) i j = 0
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => (Fin.cast h c).elim0


theorem basedTensorHom_comp (hE : ∀ q < 0, (E.X q).dim = 0) (hE' : ∀ q < 0, (E'.X q).dim = 0)
    (hE'' : ∀ q < 0, (E''.X q).dim = 0) (hC' : ∀ q < 0, (C'.X q).dim = 0) (d e d' e' : ℤ)
    (f : ∀ r, C.X r ⟶ C'.X (r + d)) (g : ∀ r, E.X r ⟶ E'.X (r + e))
    (f' : ∀ r, C'.X r ⟶ C''.X (r + d')) (g' : ∀ r, E'.X r ⟶ E''.X (r + e')) (r : ℤ) :
    basedTensorHom hE hE' d e f g r ≫ basedTensorHom hE' hE'' d' e' f' g' (r + (d + e)) =
      (e' * d).negOnePow • (basedTensorHom hE hE'' (d + d') (e + e')
        (fun a => f a ≫ f' (a + d) ≫ eqToHom (congrArg C''.X (by ring)))
        (fun c => g c ≫ g' (c + e) ≫ eqToHom (congrArg E''.X (by ring))) r ≫
        eqToHom (congrArg (basedComplexTensor C'' E'' hE'').X (by ring))) := by
  refine block_ext fun p q => ?_
  have hR := blk_smul_eqToHom hE hE'' (basedTensorHom hE hE'' (d + d') (e + e')
      (fun a => f a ≫ f' (a + d) ≫ eqToHom (congrArg C''.X (show a + d + d' = a + (d + d') by ring)))
      (fun c => g c ≫ g' (c + e) ≫ eqToHom (congrArg E''.X (show c + e + e' = c + (e + e') by ring)))
      r) (show r + ((d + d') + (e + e')) = r + (d + e) + (d' + e') by ring) ((e' * d).negOnePow) p q
  refine (blk_comp hE hE' hE'' _ _ p q).trans (Eq.trans ?_ hR.symm)
  rw [blockInc_comp_basedTensorHom_comp_blockProj hE hE'' (d + d') (e + e') _ _ r p _]
  simp only [blockInc_comp_basedTensorHom_comp_blockProj hE hE' d e f g r, blockInc_comp_basedTensorHom_comp_blockProj hE' hE'' d' e' f' g' (r + (d + e))]
  simp only [Fin.coe_cast]
  by_cases hq : ((q : ℕ) : ℤ) = (p : ℕ) + (d + d')
  · by_cases hin : 0 ≤ ((p : ℕ) : ℤ) + d ∧ ((p : ℕ) : ℤ) + d ≤ ((r + (d + e)).toNat : ℤ)
    · obtain ⟨hin1, hin2⟩ := hin
      set p0 : Fin ((r + (d + e)).toNat + 1) := ⟨(((p : ℕ) : ℤ) + d).toNat, by omega⟩ with hp0def
      have hp0 : ((p0 : ℕ) : ℤ) = (p : ℕ) + d := by simp only [hp0def]; omega
      rw [Finset.sum_eq_single p0]
      · rw [dif_pos hp0, dif_pos (show ((q : ℕ) : ℤ) = (p0 : ℕ) + d' by omega), dif_pos hq]
        rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Linear.units_smul_comp,
          smul_smul]
        have hs : (e * ((p : ℕ) : ℤ)).negOnePow * (e' * ((p0 : ℕ) : ℤ)).negOnePow =
            (e' * d).negOnePow * ((e + e') * ((p : ℕ) : ℤ)).negOnePow := by
          rw [hp0, ← Int.negOnePow_add, ← Int.negOnePow_add]; congr 1; ring
        rw [hs]
        congr 1
        simp only [Category.assoc]
        rw [kron_transport_assoc f' g' hp0.symm (show r - ((p : ℕ) : ℤ) + e =
            r + (d + e) - ((p0 : ℕ) : ℤ) by omega), basedKron_comp_basedKron_assoc, kron_split]
        simp only [Category.assoc, eqToHom_trans]
      · intro b _ hb
        rw [dif_neg (fun h => hb (Fin.ext (by omega))), zero_comp]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero, dif_pos hq]
      · rw [not_and_or] at hin
        rcases hin with hin | hin
        · rw [comp_zero_of_dim (f (p : ℕ)) _ (hC' _ (by omega)), basedKron_eq_zero (Or.inl rfl), zero_comp,
            smul_zero, zero_comp, smul_zero]
        · rw [comp_zero_of_dim (g (r - (p : ℕ))) _ (hE' _ (by omega)), basedKron_eq_zero (Or.inr rfl),
            zero_comp, smul_zero, zero_comp, smul_zero]
      · intro b _
        rw [dif_neg (fun h => hin ⟨by omega, by omega⟩), zero_comp]
  · rw [dif_neg hq, zero_comp, smul_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : ((b : ℕ) : ℤ) = (p : ℕ) + d
    · rw [dif_pos hb, dif_neg (fun h => hq (by omega)), comp_zero]
    · rw [dif_neg hb, zero_comp]

end HSP.ChainModels
