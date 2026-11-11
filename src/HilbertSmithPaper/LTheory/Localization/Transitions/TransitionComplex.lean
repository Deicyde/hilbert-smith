import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BoxPairingPow
import HilbertSmithPaper.LTheory.Localization.Products.ProductDualityMap
import HilbertSmithPaper.LTheory.Localization.Products.ProductEquivalence
import HilbertSmithPaper.LTheory.Localization.Products.ProductInvolution
import HilbertSmithPaper.LTheory.Localization.Products.ProductLeibniz
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLinePoincare
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.DualComplexFinite
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductTotal
import HilbertSmithPaper.LTheory.Base.Complexes.FiniteBounded

/-!
# Product of a complex with the line

For a strict `m`-dimensional symmetric Poincaré complex `(C, φ)` in `Kar C_{ℤ^j} A`, the product
`(C ⊗ Λ, φ ⊗ λ)` for the box product pairing is a strict `m'`-dimensional symmetric Poincaré
complex in `Kar C_{ℤ^{j+1}} A` (`m' = m + 1`): its chain objects vanish outside `[0, m + 1]`,
`T(φ ⊗ λ) = Tφ ⊗ Tλ`, `∂(φ ⊗ λ) = ∂φ ⊗ λ ± φ ⊗ ∂λ = 0`, and
`(φ ⊗ λ)_♮ = (φ_♮ ⊗ λ_♮) ∘ Ξ` is a chain homotopy equivalence.

Lean: the target degree is a parameter `m'` with `m + 1 = m'`. The finiteness of the nonzero
chain objects, needed to form the products, follows from boundedness.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

universe v u

section General

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

private lemma tensor_zero_left (P : DualityPairing B E B'') {N N' : B} {V V' : E}
    (g : V ⟶ V') : P.tensor.map ((0 : N ⟶ N') ×ₘ g) = 0 := by
  simpa using P.map_smul_left 0 (0 : N ⟶ N') g

private lemma strProd_zero_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (θ : (StructureCx D).X n) (k : ℤ)
    (hk : m + n = k) : strProd P hC hD (0 : (StructureCx C).X m) θ k hk = 0 := by
  funext x
  show strProd P hC hD (0 : (StructureCx C).X m) θ k hk x = 0
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [show (0 : (StructureCx C).X m) ⟨(y.1, m - y.1), by ring⟩ = 0 from rfl, tensor_zero_left,
    zero_comp, comp_zero, comp_zero, smul_zero]

private lemma tensor_zero_right (P : DualityPairing B E B'') {N N' : B} {V V' : E}
    (f : N ⟶ N') : P.tensor.map (f ×ₘ (0 : V ⟶ V')) = 0 := by
  simpa using P.map_smul_right 0 f (0 : V ⟶ V')

private lemma strProd_zero_right (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m) (k : ℤ)
    (hk : m + n = k) : strProd P hC hD φ (0 : (StructureCx D).X n) k hk = 0 := by
  funext x
  show strProd P hC hD φ (0 : (StructureCx D).X n) k hk x = 0
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [show (0 : (StructureCx D).X n) ⟨(y.2, n - y.2), by ring⟩ = 0 from rfl, tensor_zero_right,
    zero_comp, comp_zero, comp_zero, smul_zero]

end General

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The symmetric line has finitely many nonzero chain objects. -/
private lemma symLine_finite : {r | ¬ IsZero (symLine.X r)}.Finite :=
  finite_of_bounded (k := 1) fun r hr => symLine.isZero_X (by omega)

/-- The chain objects of `C ⊗ Λ` vanish outside `[0, m + 1]` when those of `C` vanish outside
`[0, m]`. -/
private lemma isZero_prod_line {j : ℕ} {C : ChainComplex (Karoubi (BoundedPow A j)) ℤ} {m : ℤ}
    (hC : ∀ r : ℤ, r < 0 ∨ m < r → IsZero (C.X r)) (r : ℤ) (hr : r < 0 ∨ m + 1 < r) :
    IsZero ((cxProd (boxPairingPow A j) C symLine (finite_of_bounded hC) symLine_finite).X r) := by
  rw [IsZero.iff_id_eq_zero, ← cxProd.total]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [cxProd.mem_supp] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  exfalso
  have hp : 0 ≤ x.1 ∧ x.1 ≤ m := by
    by_contra h
    exact h1 (hC _ (by omega))
  have hq : x.2 = 0 ∨ x.2 = 1 := by
    by_contra h
    exact h2 (symLine.isZero_X h)
  omega

/-- The product `(C ⊗ Λ, φ ⊗ λ)` of a strict `m`-dimensional symmetric Poincaré complex with the
symmetric line, a strict `m'`-dimensional one (`m' = m + 1`). -/
noncomputable def transitionCx {j : ℕ} {m m' : ℤ} (hm : m + 1 = m')
    (x : SymPoincare (Karoubi (BoundedPow A j)) m) :
    SymPoincare (Karoubi (BoundedPow A (j + 1))) m' where
  C := cxProd (boxPairingPow A j) x.C symLine (finite_of_bounded x.bounded) symLine_finite
  φ := strProd (boxPairingPow A j) (finite_of_bounded x.bounded) symLine_finite x.φ symLine.str
    m' hm
  bounded r hr := isZero_prod_line x.bounded r (by omega)
  cycle := by
    have hl : (StructureCx symLine).d 1 (1 - 1) symLine.str = 0 := symLine.str_T_and_cycle.2
    rw [strProd_boundary, x.cycle, hl, strProd_zero_left, strProd_zero_right, smul_zero,
      add_zero]
  symmetric := by
    rw [strProd_T, x.symmetric, symLine.str_T_and_cycle.1]
  poincare := by
    have hl : (StructureCx symLine).d 1 (1 - 1) symLine.str = 0 := symLine.str_T_and_cycle.2
    obtain ⟨e, he⟩ := cxProd_homotopyEquiv (boxPairingPow A j) x.poincare symLine_poincare
      (dualCx_finite (finite_of_bounded x.bounded) m) (dualCx_finite symLine_finite 1)
      (finite_of_bounded x.bounded) symLine_finite
    refine ⟨(HomotopyEquiv.ofIso (prodDualIso (boxPairingPow A j) (finite_of_bounded x.bounded)
      symLine_finite m 1 m' hm)).trans e, ?_⟩
    rw [strProd_toHom (boxPairingPow A j) _ _ x.φ symLine.str x.cycle hl]
    change _ ≫ e.hom = _
    rw [he]
    rfl

end HSP
