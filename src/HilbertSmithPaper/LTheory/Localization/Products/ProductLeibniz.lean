import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductDualHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductDifferential

/-!
# Leibniz rule for products

`∂(φ ⊗ θ) = ∂φ ⊗ θ + (-1)^m φ ⊗ ∂θ` for `φ ∈ M(C)_m`, `θ ∈ M(D)_n`. The degrees are written with
a parameter `k = m + n`, so the three products live in `M(C ⊗ D)_{k-1}` without transports.

The proof compares the blocks from the dual of the summand `C_c ⊠ D_d` to the summand
`C_a ⊠ D_b`: the differential of `C ⊗ D` on summands (`HSP.cxProd.d_π`) and its dual split
`∂(φ ⊗ θ)` into four terms, of which at most two survive, according to whether
`(a + c, b + d) = (m - 1, n)` or `(m, n - 1)`; there they match the blocks of `∂φ ⊗ θ` and of
`(-1)^m φ ⊗ ∂θ` by the naturality of `κ` and the sign identities of the article.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

private lemma dualHom_units_smul {M N : B''} (u : ℤˣ) (f : M ⟶ N) :
    dualHom (u • f) = u • dualHom f := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (dualHom (M := M) (N := N)) dualHom_add).map_zsmul (u : ℤ) f

section Pairing

variable (P : DualityPairing B E B'')

private lemma tensor_add_left {N N' : B} {V V' : E} (u : ℤˣ) (f f' : N ⟶ N') (g : V ⟶ V') :
    P.tensor.map ((f + u • f') ×ₘ g) = P.tensor.map (f ×ₘ g) + u • P.tensor.map (f' ×ₘ g) := by
  rw [P.map_add_left, Units.smul_def, Units.smul_def]
  congr 1
  exact (AddMonoidHom.mk' (fun f : N ⟶ N' => P.tensor.map (f ×ₘ g))
    fun f f' => P.map_add_left f f' g).map_zsmul (u : ℤ) f'

private lemma tensor_add_right {N N' : B} {V V' : E} (u : ℤˣ) (f : N ⟶ N') (g g' : V ⟶ V') :
    P.tensor.map (f ×ₘ (g + u • g')) = P.tensor.map (f ×ₘ g) + u • P.tensor.map (f ×ₘ g') := by
  rw [P.map_add_right, Units.smul_def, Units.smul_def]
  congr 1
  exact (AddMonoidHom.mk' (fun g : V ⟶ V' => P.tensor.map (f ×ₘ g))
    fun g g' => P.map_add_right f g g').map_zsmul (u : ℤ) g'

private lemma tensor_comp_left {N N' N'' : B} {V V' : E} (f : N ⟶ N') (f' : N' ⟶ N'')
    (g : V ⟶ V') :
    P.tensor.map (f ×ₘ g) ≫ P.tensor.map (f' ×ₘ 𝟙 V') = P.tensor.map ((f ≫ f') ×ₘ g) := by
  rw [← P.tensor.map_comp]
  congr 1
  exact Prod.ext rfl (Category.comp_id g)

private lemma tensor_comp_right {N N' : B} {V V' V'' : E} (f : N ⟶ N') (g : V ⟶ V')
    (g' : V' ⟶ V'') :
    P.tensor.map (f ×ₘ g) ≫ P.tensor.map (𝟙 N' ×ₘ g') = P.tensor.map (f ×ₘ (g ≫ g')) := by
  rw [← P.tensor.map_comp]
  congr 1
  exact Prod.ext (Category.comp_id f) rfl

private lemma left_comp_tensor {N₀ N N' : B} {V V' : E} (f₀ : N₀ ⟶ N) (f : N ⟶ N')
    (g : V ⟶ V') :
    P.tensor.map (f₀ ×ₘ 𝟙 V) ≫ P.tensor.map (f ×ₘ g) = P.tensor.map ((f₀ ≫ f) ×ₘ g) := by
  rw [← P.tensor.map_comp]
  congr 1
  exact Prod.ext rfl (Category.id_comp g)

private lemma right_comp_tensor {N N' : B} {V₀ V V' : E} (g₀ : V₀ ⟶ V) (f : N ⟶ N')
    (g : V ⟶ V') :
    P.tensor.map (𝟙 N ×ₘ g₀) ≫ P.tensor.map (f ×ₘ g) = P.tensor.map (f ×ₘ (g₀ ≫ g)) := by
  rw [← P.tensor.map_comp]
  congr 1
  exact Prod.ext (Category.id_comp f) rfl

private lemma κ_natural_left {N N' : B} (f : N ⟶ N') (V : E) {Z : B''}
    (h : P.tensor.obj (dual N, dual V) ⟶ Z) :
    dualHom (P.tensor.map (f ×ₘ 𝟙 V)) ≫ (P.κ N V).hom ≫ h =
      (P.κ N' V).hom ≫ P.tensor.map (dualHom f ×ₘ 𝟙 (dual V)) ≫ h := by
  rw [← Category.assoc, P.κ_natural, dualHom_id, Category.assoc]

private lemma κ_natural_right (N : B) {V V' : E} (g : V ⟶ V') {Z : B''}
    (h : P.tensor.obj (dual N, dual V) ⟶ Z) :
    dualHom (P.tensor.map (𝟙 N ×ₘ g)) ≫ (P.κ N V).hom ≫ h =
      (P.κ N V').hom ≫ P.tensor.map (𝟙 (dual N) ×ₘ dualHom g) ≫ h := by
  rw [← Category.assoc, P.κ_natural, dualHom_id, Category.assoc]

variable {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite)

private lemma dualπ_d {c d s s₁ c₁ d₁ : ℤ} (hs : s + 1 = s₁) (h : c + d = s) (hc : c + 1 = c₁)
    (hd : d + 1 = d₁) :
    dualHom (cxProd.π P hC hD c d s) ≫ dualHom ((cxProd P C D hC hD).d s₁ s) =
      dualHom (P.tensor.map (C.d c₁ c ×ₘ 𝟙 (D.X d))) ≫ dualHom (cxProd.π P hC hD c₁ d s₁) +
        c.negOnePow • (dualHom (P.tensor.map (𝟙 (C.X c) ×ₘ D.d d₁ d)) ≫
          dualHom (cxProd.π P hC hD c d₁ s₁)) := by
  rw [← dualHom_comp, cxProd.d_π P hC hD hs h hc hd, dualHom_add, dualHom_units_smul,
    dualHom_comp, dualHom_comp]

end Pairing

/-- **Leibniz rule for products.** `∂(φ ⊗ θ) = ∂φ ⊗ θ + (-1)^m φ ⊗ ∂θ`. -/
theorem strProd_boundary (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    (StructureCx (cxProd P C D hC hD)).d k (k - 1) (strProd P hC hD φ θ k hk) =
      strProd P hC hD ((StructureCx C).d m (m - 1) φ) θ (k - 1) (by omega) +
        m.negOnePow • strProd P hC hD φ ((StructureCx D).d n (n - 1) θ) (k - 1) (by omega) := by
  funext x
  obtain ⟨⟨r, s⟩, hrs⟩ := x
  change ((StructureCx (cxProd P C D hC hD)).d k (k - 1) (strProd P hC hD φ θ k hk))
      ⟨(r, s), hrs⟩ =
    strProd P hC hD ((StructureCx C).d m (m - 1) φ) θ (k - 1) (by omega) ⟨(r, s), hrs⟩ +
      m.negOnePow • strProd P hC hD φ ((StructureCx D).d n (n - 1) θ) (k - 1) (by omega)
        ⟨(r, s), hrs⟩
  rw [StructureCx.d_apply _ k (k - 1) _ r s hrs (r + 1) (s + 1) (by omega) (by omega)]
  refine cxProd.hom_ext_to P hC hD fun a b hab => ?_
  refine cxProd.dual_hom_ext P hC hD fun c d hcd => ?_
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  rw [cxProd.d_π P hC hD (r := r + 1) (r' := r) (p₁ := a + 1) (q₁ := b + 1) rfl hab rfl rfl,
    ← Category.assoc (dualHom _) (dualHom _),
    dualπ_d P hC hD (s₁ := s + 1) (c₁ := c + 1) (d₁ := d + 1) rfl hcd rfl rfl]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  by_cases hA : a + c = m - 1 ∧ b + d = n
  · obtain ⟨ha, hb⟩ := hA
    rw [reassoc_of% (strProd_block P hC hD φ θ k hk (r := r + 1) (s := s) (a := a + 1) (b := b)
        (c := c) (d := d) (by omega) (by omega) (by omega) hb),
      reassoc_of% (strProd_block_of_ne P hC hD φ θ k hk (r := r + 1) (s := s) (a := a)
        (b := b + 1) (c := c) (d := d) (by omega) (by omega)),
      strProd_block P hC hD φ θ k hk (r := r) (s := s + 1) (a := a) (b := b) (c := c + 1) (d := d)
        (by omega) hab (by omega) hb,
      strProd_block_of_ne P hC hD φ θ k hk (r := r) (s := s + 1) (a := a) (b := b) (c := c)
        (d := d + 1) (by omega) (by omega),
      strProd_block P hC hD _ θ (k - 1) _ (r := r) (s := s) (a := a) (b := b) (c := c) (d := d)
        hrs hab ha hb,
      strProd_block_of_ne P hC hD φ _ (k - 1) _ (r := r) (s := s) (a := a) (b := b) (c := c)
        (d := d) hrs (by omega)]
    erw [StructureCx.dHom_apply C m (m - 1) φ a c ha (a + 1) (c + 1) (by omega) (by omega)]
    simp only [zero_comp, comp_zero, smul_zero, add_zero, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, tensor_comp_left, κ_natural_left, left_comp_tensor,
      tensor_add_left, Preadditive.comp_add, smul_add, smul_smul]
    subst hab
    congr 2
    · exact (Int.negOnePow_eq_iff _ _).2 ⟨b, by ring⟩
    · rw [← Int.negOnePow_add, ← Int.negOnePow_add]
      exact (Int.negOnePow_eq_iff _ _).2 ⟨b, by ring⟩
  by_cases hB : a + c = m ∧ b + d = n - 1
  · obtain ⟨ha, hb⟩ := hB
    rw [reassoc_of% (strProd_block_of_ne P hC hD φ θ k hk (r := r + 1) (s := s) (a := a + 1)
        (b := b) (c := c) (d := d) (by omega) (by omega)),
      reassoc_of% (strProd_block P hC hD φ θ k hk (r := r + 1) (s := s) (a := a) (b := b + 1)
        (c := c) (d := d) (by omega) (by omega) ha (by omega)),
      strProd_block_of_ne P hC hD φ θ k hk (r := r) (s := s + 1) (a := a) (b := b) (c := c + 1)
        (d := d) (by omega) (by omega),
      strProd_block P hC hD φ θ k hk (r := r) (s := s + 1) (a := a) (b := b) (c := c) (d := d + 1)
        (by omega) hab ha (by omega),
      strProd_block_of_ne P hC hD _ θ (k - 1) _ (r := r) (s := s) (a := a) (b := b) (c := c)
        (d := d) hrs (by omega),
      strProd_block P hC hD φ _ (k - 1) _ (r := r) (s := s) (a := a) (b := b) (c := c) (d := d)
        hrs hab ha hb]
    erw [StructureCx.dHom_apply D n (n - 1) θ b d hb (b + 1) (d + 1) (by omega) (by omega)]
    simp only [zero_comp, comp_zero, zero_add, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, tensor_comp_right, κ_natural_right,
      right_comp_tensor, tensor_add_right, Preadditive.comp_add, smul_add, smul_smul]
    subst hab
    congr 2
    · rw [← Int.negOnePow_add, ← Int.negOnePow_add]
      exact (Int.negOnePow_eq_iff _ _).2 ⟨a, by ring⟩
    · rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
      exact (Int.negOnePow_eq_iff _ _).2 ⟨0, by linear_combination ha⟩
  rw [reassoc_of% (strProd_block_of_ne P hC hD φ θ k hk (r := r + 1) (s := s) (a := a + 1)
      (b := b) (c := c) (d := d) (by omega) (by omega)),
    reassoc_of% (strProd_block_of_ne P hC hD φ θ k hk (r := r + 1) (s := s) (a := a) (b := b + 1)
      (c := c) (d := d) (by omega) (by omega)),
    strProd_block_of_ne P hC hD φ θ k hk (r := r) (s := s + 1) (a := a) (b := b) (c := c + 1)
      (d := d) (by omega) (by omega),
    strProd_block_of_ne P hC hD φ θ k hk (r := r) (s := s + 1) (a := a) (b := b) (c := c)
      (d := d + 1) (by omega) (by omega),
    strProd_block_of_ne P hC hD _ θ (k - 1) _ (r := r) (s := s) (a := a) (b := b) (c := c)
      (d := d) hrs (by omega),
    strProd_block_of_ne P hC hD φ _ (k - 1) _ (r := r) (s := s) (a := a) (b := b) (c := c)
      (d := d) hrs (by omega)]
  simp only [zero_comp, comp_zero, smul_zero, add_zero]

end HSP
