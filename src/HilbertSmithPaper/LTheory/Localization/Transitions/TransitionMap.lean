import Mathlib
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd
import HilbertSmithPaper.LTheory.Base.Groups.HomotopyIsometryInvariance
import HilbertSmithPaper.LTheory.Base.Pairs.PairTransport
import HilbertSmithPaper.LTheory.Localization.Products.ProductWithLine
import HilbertSmithPaper.LTheory.Localization.Products.ProductPush
import HilbertSmithPaper.LTheory.Localization.Products.ProductInvolution
import HilbertSmithPaper.LTheory.Localization.Products.ProductLeibniz
import HilbertSmithPaper.LTheory.Localization.Products.ProductDualityMap
import HilbertSmithPaper.LTheory.Localization.Products.ProductEquivalence
import HilbertSmithPaper.LTheory.Localization.Transitions.LowerLGroup

/-!
# Transition map

For `j ≥ 0` and `m ∈ ℤ`, the transition map
`t : L^p_m(C_{ℤ^j} A) → L^p_{m+1}(C_{ℤ^{j+1}} A)`, `[C, φ] ↦ [C ⊗ Λ, φ ⊗ λ]`, a homomorphism.
For `m = k + j` it is a homomorphism `L^{⟨-j⟩}_k(A) → L^{⟨-j-1⟩}_k(A)`.

Lean: the target degree is a parameter `m'` with `m + 1 = m'`, so that the lower-L-group version
needs no transport along `k + j + 1 = k + (j + 1)`. Products are taken for the box product pairing
`HSP.boxPairingPow A j`. The finiteness of the nonzero chain objects, needed to form the products,
follows from boundedness.
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

omit [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B] in
/-- A complex whose chain objects vanish outside `[0, k]` has finitely many nonzero ones. -/
private lemma finite_of_bounded {C : ChainComplex B ℤ} {k : ℤ}
    (h : ∀ r : ℤ, r < 0 ∨ k < r → IsZero (C.X r)) : {r | ¬ IsZero (C.X r)}.Finite :=
  (Set.finite_Icc 0 k).subset fun r hr => by
    by_contra h'
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h'
    exact hr (h r (by omega))

private lemma strProd_add_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ φ' : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    strProd P hC hD (φ + φ') θ k hk = strProd P hC hD φ θ k hk + strProd P hC hD φ' θ k hk := by
  funext x
  show strProd P hC hD (φ + φ') θ k hk x =
    strProd P hC hD φ θ k hk x + strProd P hC hD φ' θ k hk x
  simp only [strProd, Pi.add_apply, P.map_add_left, Preadditive.add_comp, Preadditive.comp_add,
    smul_add, Finset.sum_add_distrib]

private lemma strProd_zero_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (θ : (StructureCx D).X n) (k : ℤ)
    (hk : m + n = k) : strProd P hC hD (0 : (StructureCx C).X m) θ k hk = 0 := by
  have h := strProd_add_left P hC hD (0 : (StructureCx C).X m) 0 θ k hk
  rw [add_zero] at h
  simpa using h.symm

private lemma strProd_neg_left (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m)
    (θ : (StructureCx D).X n) (k : ℤ) (hk : m + n = k) :
    strProd P hC hD (-φ) θ k hk = -strProd P hC hD φ θ k hk := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← strProd_add_left, neg_add_cancel, strProd_zero_left]

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
    have hl : (StructureCx symLine).d 1 (1 - 1) symLine.str = 0 := symLine.str_cycle
    rw [strProd_boundary, x.cycle, hl, strProd_zero_left, strProd_zero_right, smul_zero,
      add_zero]
  symmetric := by
    rw [strProd_T, x.symmetric, symLine.str_T]
  poincare := by
    have hl : (StructureCx symLine).d 1 (1 - 1) symLine.str = 0 := symLine.str_cycle
    obtain ⟨e, he⟩ := cxProd_homotopyEquiv (boxPairingPow A j) x.poincare symLine_poincare
      (dualCx_finite (finite_of_bounded x.bounded) m) (dualCx_finite symLine_finite 1)
      (finite_of_bounded x.bounded) symLine_finite
    refine ⟨(HomotopyEquiv.ofIso (prodDualIso (boxPairingPow A j) (finite_of_bounded x.bounded)
      symLine_finite m 1 m' hm)).trans e, ?_⟩
    rw [strProd_toHom (boxPairingPow A j) _ _ x.φ symLine.str x.cycle hl]
    change _ ≫ e.hom = _
    rw [he]
    rfl

/-- Cobordant complexes have cobordant products with the line. -/
theorem transitionCx_cobordant {j : ℕ} {m m' : ℤ} (hm : m + 1 = m')
    {x y : SymPoincare (Karoubi (BoundedPow A j)) m} (h : Cobordant x y) :
    Cobordant (transitionCx hm x) (transitionCx hm y) := by
  sorry

/-- The product with the line of a sum is homotopy-isometric to the sum of the products. -/
theorem transitionCx_sum {j : ℕ} {m m' : ℤ} (hm : m + 1 = m')
    (x y : SymPoincare (Karoubi (BoundedPow A j)) m) :
    LGroup.mk (transitionCx hm (x.sum y)) =
      LGroup.mk ((transitionCx hm x).sum (transitionCx hm y)) := by
  sorry

/-- **Transition map.** `t : L^p_m(C_{ℤ^j} A) → L^p_{m'}(C_{ℤ^{j+1}} A)`,
`[C, φ] ↦ [C ⊗ Λ, φ ⊗ λ]` (`m' = m + 1`), a homomorphism. -/
noncomputable def transitionMap (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (j : ℕ) {m m' : ℤ} (hm : m + 1 = m') :
    Lp (BoundedPow A j) m →+ Lp (BoundedPow A (j + 1)) m' :=
  AddMonoidHom.mk' (Quotient.lift (fun x => LGroup.mk (transitionCx hm x))
    fun _ _ h => Quotient.sound (transitionCx_cobordant hm h)) fun a b => by
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact transitionCx_sum hm _ _

/-- The value of `t` on a class: `t [C, φ] = [C ⊗ Λ, φ ⊗ λ]`. -/
lemma transitionMap_mk (j : ℕ) {m m' : ℤ} (hm : m + 1 = m')
    (x : SymPoincare (Karoubi (BoundedPow A j)) m) :
    transitionMap A j hm (LGroup.mk x) = LGroup.mk (transitionCx hm x) :=
  rfl

/-- The transition map on lower L-groups, `L^{⟨-j⟩}_k(A) → L^{⟨-j-1⟩}_k(A)`. -/
noncomputable def transitionLower (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A]
    [HasFiniteBiproducts A] [DualCat A] (j : ℕ) (k : ℤ) : lowerL A j k →+ lowerL A (j + 1) k :=
  transitionMap A j (m := k + j) (m' := k + ↑(j + 1)) (by push_cast; ring)

end HSP
