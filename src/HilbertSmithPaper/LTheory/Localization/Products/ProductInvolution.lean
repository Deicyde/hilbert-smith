import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Base.Complexes.StructureInvolution
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductDualHomExt

/-!
# Products commute with T

`T(φ ⊗ θ) = Tφ ⊗ Tθ` for `φ ∈ M(C)_m`, `θ ∈ M(D)_n`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace HSP

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

open DualCat

private lemma dualHom_units_smul' {M N : B''} (u : ℤˣ) (f : M ⟶ N) :
    dualHom (u • f) = u • dualHom f := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (dualHom (M := M) (N := N)) dualHom_add).map_zsmul (u : ℤ) f

private lemma tensor_smul_smul (P : DualityPairing B E B'') {N N' : B} {V V' : E} (u v : ℤˣ)
    (f : N ⟶ N') (g : V ⟶ V') :
    P.tensor.map ((u • f) ×ₘ (v • g)) = (u * v) • P.tensor.map (f ×ₘ g) := by
  have h1 : P.tensor.map ((u • f) ×ₘ (v • g)) = u • P.tensor.map (f ×ₘ (v • g)) := by
    rw [Units.smul_def, Units.smul_def]
    exact (AddMonoidHom.mk' (fun f : N ⟶ N' => P.tensor.map (f ×ₘ (v • g)))
      fun f f' => P.map_add_left f f' _).map_zsmul (u : ℤ) f
  have h2 : P.tensor.map (f ×ₘ (v • g)) = v • P.tensor.map (f ×ₘ g) := by
    rw [Units.smul_def, Units.smul_def]
    exact (AddMonoidHom.mk' (fun g : V ⟶ V' => P.tensor.map (f ×ₘ g))
      fun g g' => P.map_add_right f g g').map_zsmul (v : ℤ) g
  rw [h1, h2, smul_smul]

private lemma tensor_eqToHom (P : DualityPairing B E B'') {N N' : B} {V V' : E} (h₁ : N = N')
    (h₂ : V = V') :
    P.tensor.map (eqToHom h₁ ×ₘ eqToHom h₂) = eqToHom (by rw [h₁, h₂]) := by
  subst h₁ h₂
  simp

private lemma dual_block {X Y A A' : B''} (F : dual X ⟶ Y) (πs : Y ⟶ A) (πr : X ⟶ A') :
    dualHom πs ≫ (dualHom F ≫ eqToHom (dual_dual X)) ≫ πr =
      dualHom (dualHom πr ≫ F ≫ πs) ≫ eqToHom (dual_dual A') := by
  rw [dualHom_comp, dualHom_comp, dualHom_dualHom]
  simp

/-- **Products commute with T.** `T(φ ⊗ θ) = Tφ ⊗ Tθ`. -/
theorem strProd_T (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    (StructureCx.T (cxProd P C D hC hD)).f k (strProd P hC hD φ θ k hk) =
      strProd P hC hD ((StructureCx.T C).f m φ) ((StructureCx.T D).f n θ) k hk := by
  funext x
  obtain ⟨⟨r, s⟩, hrs⟩ := x
  rw [StructureCx.T_apply]
  refine cxProd.hom_ext_to P hC hD fun a b hab => ?_
  refine cxProd.dual_hom_ext P hC hD fun c d hcd => ?_
  by_cases hm : a + c = m ∧ b + d = n
  · obtain ⟨ha, hb⟩ := hm
    rw [strProd_block P hC hD _ _ k hk hrs hab ha hb, StructureCx.T_apply, StructureCx.T_apply,
      tensor_smul_smul]
    dsimp only
    rw [Linear.units_smul_comp, Linear.comp_units_smul, dual_block,
      strProd_block P hC hD φ θ k hk (r := s) (s := r) (a := c) (b := d) (c := a) (d := b)
        (by omega) hcd (by omega) (by omega),
      dualHom_units_smul', dualHom_comp, P.κ_dual, Linear.units_smul_comp, Category.assoc,
      Category.assoc, ← Category.assoc (dualHom _), P.κ_natural]
    rw [show (dualHom (φ ⟨(c, a), by omega⟩) ≫ eqToHom (dual_dual (C.X a))) ×ₘ
        (dualHom (θ ⟨(d, b), by omega⟩) ≫ eqToHom (dual_dual (D.X b))) =
        (dualHom (φ ⟨(c, a), by omega⟩) ×ₘ dualHom (θ ⟨(d, b), by omega⟩)) ≫
          (eqToHom (dual_dual (C.X a)) ×ₘ eqToHom (dual_dual (D.X b))) from rfl,
      P.tensor.map_comp, tensor_eqToHom, Linear.comp_units_smul, smul_smul, smul_smul]
    simp only [Category.assoc, eqToHom_trans]
    congr 1
    obtain rfl : r = a + b := hab.symm
    obtain rfl : s = c + d := hcd.symm
    obtain rfl : m = a + c := ha.symm
    obtain rfl : n = b + d := hb.symm
    simp only [← Int.negOnePow_add]
    rw [Int.negOnePow_eq_iff]
    exact ⟨a * d + d * c - a * b, by ring⟩
  · rw [strProd_block_of_ne P hC hD _ _ k hk hrs hm]
    dsimp only
    rw [Linear.units_smul_comp, Linear.comp_units_smul, dual_block,
      strProd_block_of_ne P hC hD φ θ k hk (r := s) (s := r) (a := c) (b := d) (c := a) (d := b)
        (by omega) (by omega), dualHom_zero, zero_comp, smul_zero]

end HSP
