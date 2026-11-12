import Mathlib
import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory
import HilbertSmithPaper.LTheory.Localization.Line.LineProductBounds
import HilbertSmithPaper.LTheory.Localization.Line.ProductLinePairMap
import HilbertSmithPaper.LTheory.Localization.Products.BoxPairingPow
import HilbertSmithPaper.LTheory.Localization.Products.ExternalProduct
import HilbertSmithPaper.LTheory.Localization.Products.ProductPush
import HilbertSmithPaper.LTheory.Localization.Products.SymmetricLineStructure
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductMap
import HilbertSmithPaper.LTheory.Localization.Transitions.TransitionComplex
import HilbertSmithPaper.LTheory.Base.Complexes.FiniteBounded
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushId

/-!
# Product of a pair with the line

For a strict `k`-dimensional symmetric Poincaré pair `(f : C ⟶ D, δφ, φ)` in `Kar C_{ℤ^j} A`,
`(f ⊗ 1 : C ⊗ Λ ⟶ D ⊗ Λ, δφ ⊗ λ, φ ⊗ λ)` is a strict `(k+1)`-dimensional symmetric Poincaré
pair in `Kar C_{ℤ^{j+1}} A`, with boundary `(C ⊗ Λ, φ ⊗ λ)` (no sign). The products are taken
for the box product pairing `Kar C_{ℤ^j} A × C_ℤ(ℚ) → Kar C_{ℤ^{j+1}} A`.

Lean: the finiteness of the nonzero chain objects, needed to form the products, is a hypothesis
(any proof will do).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

section General

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear ℚ E] [HasFiniteBiproducts E]
  [DualCat E]
  {B'' : Type u₃} [Category.{v₃} B''] [Preadditive B''] [Linear ℚ B''] [HasFiniteBiproducts B'']
  [DualCat B'']

private lemma tensor_zero_right' (P : DualityPairing B E B'') {N N' : B} {V V' : E}
    (f : N ⟶ N') : P.tensor.map (f ×ₘ (0 : V ⟶ V')) = 0 := by
  simpa using P.map_smul_right 0 f (0 : V ⟶ V')

private lemma strProd_zero_right' (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {m n : ℤ} (φ : (StructureCx C).X m) (k : ℤ)
    (hk : m + n = k) : strProd P hC hD φ (0 : (StructureCx D).X n) k hk = 0 := by
  funext x
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [show (0 : (StructureCx D).X n) ⟨(y.2, n - y.2), by ring⟩ = 0 from rfl, tensor_zero_right',
    zero_comp, comp_zero, comp_zero, smul_zero]

/-- The boundary of a structure evaluated at a block does not depend on the target index. -/
private lemma d_congr {C : ChainComplex B ℤ} {n m m' : ℤ} (hm : m = m') (y : (StructureCx C).X n)
    (p q : ℤ) (h : p + q = m) (h' : p + q = m') :
    (StructureCx C).d n m y ⟨(p, q), h⟩ = (StructureCx C).d n m' y ⟨(p, q), h'⟩ := by
  subst hm
  rfl

/-- A product with a boundary does not depend on the target index of the boundary. -/
private lemma strProd_d_congr (P : DualityPairing B E B'') {C : ChainComplex B ℤ}
    {D : ChainComplex E ℤ} (hC : {r | ¬ IsZero (C.X r)}.Finite)
    (hD : {r | ¬ IsZero (D.X r)}.Finite) {n m m' l : ℤ} (hm : m = m') (y : (StructureCx C).X n)
    (θ : (StructureCx D).X l) (k k' : ℤ) (hk : m + l = k) (hk' : m' + l = k')
    (p q : ℤ) (h : p + q = k) (h' : p + q = k') :
    strProd P hC hD ((StructureCx C).d n m y) θ k hk ⟨(p, q), h⟩ =
      strProd P hC hD ((StructureCx C).d n m' y) θ k' hk' ⟨(p, q), h'⟩ := by
  subst hm hk hk'
  rfl

end General

/-- **Product of a pair with the line.** `(f ⊗ 1, δφ ⊗ λ, φ ⊗ λ)` is a strict
`(n+1)`-dimensional symmetric Poincaré pair with boundary `(C ⊗ Λ, φ ⊗ λ)`. -/
theorem SymPair.exists_prod_line {j : ℕ} {m n : ℤ} (W : SymPair (Karoubi (BoundedPow A j)) m n)
    (hC : {r | ¬ IsZero (W.C.X r)}.Finite) (hD : {r | ¬ IsZero (W.D.X r)}.Finite)
    (hΛ : {r | ¬ IsZero (symLine.X r)}.Finite) :
    ∃ W' : SymPair (Karoubi (BoundedPow A (j + 1))) (m + 1) (n + 1),
      W'.data = ⟨cxProd (boxPairingPow A j) W.C symLine hC hΛ,
        cxProd (boxPairingPow A j) W.D symLine hD hΛ,
        cxProdMap (boxPairingPow A j) W.f (𝟙 symLine) hC hΛ hD hΛ,
        strProd (boxPairingPow A j) hD hΛ W.δφ symLine.str (n + 1) rfl,
        strProd (boxPairingPow A j) hC hΛ W.φ symLine.str (m + 1) rfl⟩ := by
  have hK : {r | ¬ IsZero ((cone W.f).X r)}.Finite :=
    finite_of_bounded (k := n) fun r hr => (biprod_isZero_iff _ _).2
      ⟨W.bounded r hr, W.boundary_bounded (r - 1) (by have := W.dim; omega)⟩
  have hl : (StructureCx symLine).d 1 (1 - 1) symLine.str = 0 := symLine.str_T_and_cycle.2
  have hφ' : (StructureCx (cxProd (boxPairingPow A j) W.C symLine hC hΛ)).d (m + 1) (m + 1 - 1)
      (strProd (boxPairingPow A j) hC hΛ W.φ symLine.str (m + 1) rfl) = 0 :=
    (transitionCx rfl W.boundary).cycle
  have hδφ' : (StructureCx (cxProd (boxPairingPow A j) W.D symLine hD hΛ)).d (n + 1) (m + 1)
      (strProd (boxPairingPow A j) hD hΛ W.δφ symLine.str (n + 1) rfl) =
      (StructureCx.push (cxProdMap (boxPairingPow A j) W.f (𝟙 symLine) hC hΛ hD hΛ)).f (m + 1)
        (strProd (boxPairingPow A j) hC hΛ W.φ symLine.str (m + 1) rfl) := by
    have hdim := W.dim
    rw [strProd_push, ← W.rel, StructureCx.push_id]
    funext ⟨⟨p, q⟩, h⟩
    rw [d_congr (m' := n + 1 - 1) (by omega) _ p q h (by omega), strProd_boundary, hl,
      strProd_zero_right', smul_zero, add_zero]
    exact strProd_d_congr _ hD hΛ (by omega) _ _ _ _ _ _ p q _ h
  obtain ⟨J, -, hJ⟩ := pairMap_prod_line W.f W.dim W.δφ W.φ W.boundary_cycle W.rel hC hD hK hΛ
    hφ' hδφ'
  refine ⟨
    { C := cxProd (boxPairingPow A j) W.C symLine hC hΛ
      D := cxProd (boxPairingPow A j) W.D symLine hD hΛ
      f := cxProdMap (boxPairingPow A j) W.f (𝟙 symLine) hC hΛ hD hΛ
      δφ := strProd (boxPairingPow A j) hD hΛ W.δφ symLine.str (n + 1) rfl
      φ := strProd (boxPairingPow A j) hC hΛ W.φ symLine.str (m + 1) rfl
      dim := by have := W.dim; omega
      boundary_bounded := (transitionCx rfl W.boundary).bounded
      boundary_cycle := hφ'
      boundary_symmetric := (transitionCx rfl W.boundary).symmetric
      boundary_poincare := (transitionCx rfl W.boundary).poincare
      bounded := cxProd_line_isZero W.bounded hD hΛ
      symmetric := by rw [strProd_T, W.symmetric, symLine.str_T_and_cycle.1]
      rel := hδφ'
      poincare := ?_ }, rfl⟩
  obtain ⟨e, he⟩ := cxProd_homotopyEquiv (boxPairingPow A j) W.poincare symLine_poincare
    (dualCx_finite hD n) (dualCx_finite hΛ 1) hK hΛ
  refine ⟨(HomotopyEquiv.ofIso (prodDualIso (boxPairingPow A j) hD hΛ n 1 (n + 1) rfl)).trans
    (e.trans (HomotopyEquiv.ofIso J)), ?_⟩
  rw [hJ, ← he]
  rfl

end HSP
