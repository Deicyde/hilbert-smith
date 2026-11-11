import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.DualComplexFinite
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.ProductDualHomExt
import HilbertSmithPaper.LTheory.Localization.Products.Bookkeeping.SummandZero

/-!
# Dual of a tensor product

For a duality pairing `(⊠, κ)`, complexes `C`, `D` with finitely many nonzero chain objects,
`m n : ℤ` and `N = m + n` (written `k` with `m + n = k`), the isomorphism of complexes
`Ξ : (C ⊗ D)^{N-*} ≅ C^{m-*} ⊗ D^{n-*}` is `s(a, b) = (-1)^{b(a+m)}` times `κ` on the dual of the
summand `C_{m-a} ⊠ D_{n-b}`, which it carries to `C_{m-a}^* ⊠ D_{n-b}^*` in position `(a, b)`.

Lean: in degree `r`, `Ξ_r = ∑_{(a,b)} s(a,b) (ι_{m-a,n-b})^* ≫ κ ≫ ι_{a,b}` over the nonzero
summands of `(C^{m-*} ⊗ D^{n-*})_r`, with inverse `∑ s(a,b) π_{a,b} ≫ κ⁻¹ ≫ (π_{m-a,n-b})^*`.
The chain-map identity is checked on each pair of summands, where it reduces to
`s(a-1,b) = (-1)^b s(a,b)` and `s(a,b-1) = (-1)^{a+m} s(a,b)` together with the naturality of `κ`.
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
  (P : DualityPairing B E B'') {C : ChainComplex B ℤ} {D : ChainComplex E ℤ}
  (hC : {r | ¬ IsZero (C.X r)}.Finite) (hD : {r | ¬ IsZero (D.X r)}.Finite) (m n : ℤ)

private lemma dualHom_units_smul {M N : B''} (u : ℤˣ) (f : M ⟶ N) :
    dualHom (u • f) = u • dualHom f := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (dualHom (M := M) (N := N)) dualHom_add).map_zsmul (u : ℤ) f

private lemma tensor_units_smul_left {N N' : B} {V V' : E} (u : ℤˣ) (f : N ⟶ N') (g : V ⟶ V') :
    P.tensor.map ((u • f) ×ₘ g) = u • P.tensor.map (f ×ₘ g) := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (fun f : N ⟶ N' => P.tensor.map (f ×ₘ g))
    fun f f' => P.map_add_left f f' g).map_zsmul (u : ℤ) f

private lemma tensor_units_smul_right {N N' : B} {V V' : E} (u : ℤˣ) (f : N ⟶ N')
    (g : V ⟶ V') : P.tensor.map (f ×ₘ (u • g)) = u • P.tensor.map (f ×ₘ g) := by
  rw [Units.smul_def, Units.smul_def]
  exact (AddMonoidHom.mk' (fun g : V ⟶ V' => P.tensor.map (f ×ₘ g))
    fun g g' => P.map_add_right f g g').map_zsmul (u : ℤ) g

/-- The sign `s(a, b) = (-1)^{b(a+m)}`. -/
private abbrev sgn (a b : ℤ) : ℤˣ := (b * (a + m)).negOnePow

private lemma sgn_mul_self (a b : ℤ) : sgn m a b * sgn m a b = 1 := Int.units_mul_self _

/-- The component `Ξ_r`. -/
private noncomputable def xiHom (k r : ℤ) :
    dual ((cxProd P C D hC hD).X (k - r)) ⟶
      (cxProd P (dualCx C m) (dualCx D n) (dualCx_finite hC m) (dualCx_finite hD n)).X r :=
  ∑ z ∈ cxProd.supp (dualCx_finite hC m) (dualCx_finite hD n) r, sgn m z.1 z.2 •
    (dualHom (cxProd.ι P hC hD (m - z.1) (n - z.2) (k - r)) ≫
      (P.κ (C.X (m - z.1)) (D.X (n - z.2))).hom ≫
      cxProd.ι P (dualCx_finite hC m) (dualCx_finite hD n) z.1 z.2 r)

/-- The inverse component `Ξ_r⁻¹`. -/
private noncomputable def xiInv (k r : ℤ) :
    (cxProd P (dualCx C m) (dualCx D n) (dualCx_finite hC m) (dualCx_finite hD n)).X r ⟶
      dual ((cxProd P C D hC hD).X (k - r)) :=
  ∑ z ∈ cxProd.supp (dualCx_finite hC m) (dualCx_finite hD n) r, sgn m z.1 z.2 •
    (cxProd.π P (dualCx_finite hC m) (dualCx_finite hD n) z.1 z.2 r ≫
      (P.κ (C.X (m - z.1)) (D.X (n - z.2))).inv ≫
      dualHom (cxProd.π P hC hD (m - z.1) (n - z.2) (k - r)))

@[reassoc]
private lemma xiHom_π {k a b r : ℤ} (h : a + b = r) :
    xiHom P hC hD m n k r ≫ cxProd.π P (dualCx_finite hC m) (dualCx_finite hD n) a b r =
      sgn m a b • (dualHom (cxProd.ι P hC hD (m - a) (n - b) (k - r)) ≫
        (P.κ (C.X (m - a)) (D.X (n - b))).hom) := by
  by_cases hx : (a, b) ∈ cxProd.supp (dualCx_finite hC m) (dualCx_finite hD n) r
  · rw [xiHom, Preadditive.sum_comp, Finset.sum_eq_single (a, b)]
    · simp only [Linear.units_smul_comp, Category.assoc, cxProd.ι_π_self _ _ _ h,
        Category.comp_id]
    · rintro z _ hz
      rw [Linear.units_smul_comp, Category.assoc, Category.assoc,
        cxProd.ι_π_of_ne _ _ _ (fun h' => hz (Prod.ext h'.1 h'.2)), comp_zero, comp_zero,
        smul_zero]
    · exact fun h' => absurd hx h'
  · exact (cxProd.isZero_of_not_mem_supp P _ _ h hx).eq_of_tgt _ _

private lemma dualπ_xiHom {k a b r : ℤ} (hk : m + n = k) (h : a + b = r) :
    dualHom (cxProd.π P hC hD (m - a) (n - b) (k - r)) ≫ xiHom P hC hD m n k r =
      sgn m a b • ((P.κ (C.X (m - a)) (D.X (n - b))).hom ≫
        cxProd.ι P (dualCx_finite hC m) (dualCx_finite hD n) a b r) := by
  rw [xiHom, Preadditive.comp_sum, Finset.sum_eq_single (a, b)]
  · rw [Linear.comp_units_smul, ← Category.assoc, ← dualHom_comp,
      cxProd.ι_π_self _ _ _ (by omega), dualHom_id, Category.id_comp]
  · rintro z _ hz
    rw [Linear.comp_units_smul, ← Category.assoc, ← dualHom_comp,
      cxProd.ι_π_of_ne _ _ _ (fun h' => hz (Prod.ext (by omega) (by omega))), dualHom_zero,
      zero_comp, smul_zero]
  · intro hx
    rw [(cxProd.isZero_of_not_mem_supp P _ _ h hx).eq_of_src
      (cxProd.ι P (dualCx_finite hC m) (dualCx_finite hD n) a b r) 0]
    simp

private lemma xiInv_dualι {k a b r : ℤ} (hk : m + n = k) (h : a + b = r) :
    xiInv P hC hD m n k r ≫ dualHom (cxProd.ι P hC hD (m - a) (n - b) (k - r)) =
      sgn m a b • (cxProd.π P (dualCx_finite hC m) (dualCx_finite hD n) a b r ≫
        (P.κ (C.X (m - a)) (D.X (n - b))).inv) := by
  rw [xiInv, Preadditive.sum_comp, Finset.sum_eq_single (a, b)]
  · rw [Linear.units_smul_comp, Category.assoc, Category.assoc, ← dualHom_comp,
      cxProd.ι_π_self _ _ _ (by omega), dualHom_id, Category.comp_id]
  · rintro z _ hz
    rw [Linear.units_smul_comp, Category.assoc, Category.assoc, ← dualHom_comp,
      cxProd.ι_π_of_ne _ _ _ (fun h' => hz (Prod.ext (by omega) (by omega))), dualHom_zero,
      comp_zero, comp_zero, smul_zero]
  · intro hx
    rw [(cxProd.isZero_of_not_mem_supp P _ _ h hx).eq_of_tgt
      (cxProd.π P (dualCx_finite hC m) (dualCx_finite hD n) a b r) 0]
    simp

private lemma ι_xiInv {k a b r : ℤ} (h : a + b = r) :
    cxProd.ι P (dualCx_finite hC m) (dualCx_finite hD n) a b r ≫ xiInv P hC hD m n k r =
      sgn m a b • ((P.κ (C.X (m - a)) (D.X (n - b))).inv ≫
        dualHom (cxProd.π P hC hD (m - a) (n - b) (k - r))) := by
  by_cases hx : (a, b) ∈ cxProd.supp (dualCx_finite hC m) (dualCx_finite hD n) r
  · rw [xiInv, Preadditive.comp_sum, Finset.sum_eq_single (a, b)]
    · rw [Linear.comp_units_smul, ← Category.assoc, cxProd.ι_π_self _ _ _ h, Category.id_comp]
    · rintro z _ hz
      rw [Linear.comp_units_smul, ← Category.assoc,
        cxProd.ι_π_of_ne _ _ _ (fun h' => hz (Prod.ext h'.1.symm h'.2.symm)), zero_comp,
        smul_zero]
    · exact fun h' => absurd hx h'
  · exact (cxProd.isZero_of_not_mem_supp P _ _ h hx).eq_of_src _ _

namespace cxProd

/-- The differential on a summand: `ι_{p,q} ≫ d = (d ⊠ 1) ≫ ι_{p-1,q} + (-1)^p (1 ⊠ d) ≫ ι_{p,q-1}`
(with `p' = p - 1`, `q' = q - 1`). -/
private lemma ι_d {p q r r' p' q' : ℤ} (h : p + q = r) (hp : p' + 1 = p)
    (hq : q' + 1 = q) :
    ι P hC hD p q r ≫ (cxProd P C D hC hD).d r r' =
      P.tensor.map (C.d p p' ×ₘ 𝟙 (D.X q)) ≫ ι P hC hD p' q r' +
        p.negOnePow • (P.tensor.map (𝟙 (C.X p) ×ₘ D.d q q') ≫ ι P hC hD p q' r') := by
  have := P.hasMapBifunctor_of_finite hC hD
  have hp' : (ComplexShape.down ℤ).Rel p p' := hp
  have hq' : (ComplexShape.down ℤ).Rel q q' := hq
  rw [ι, HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ hp',
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ hq']
  have e1 : ComplexShape.ε₁ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)
      (p, q) = 1 := rfl
  have e2 : ComplexShape.ε₂ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)
      (p, q) = p.negOnePow := rfl
  rw [e1, e2, one_smul]
  rfl

/-- The differential followed by a projection:
`d ≫ π_{p,q} = π_{p+1,q} ≫ (d ⊠ 1) + (-1)^p π_{p,q+1} ≫ (1 ⊠ d)`
(with `p₁ = p + 1`, `q₁ = q + 1`). -/
private lemma d_π {p q r r' p₁ q₁ : ℤ} (hr : r' + 1 = r) (h : p + q = r') (hp : p + 1 = p₁)
    (hq : q + 1 = q₁) :
    (cxProd P C D hC hD).d r r' ≫ π P hC hD p q r' =
      π P hC hD p₁ q r ≫ P.tensor.map (C.d p₁ p ×ₘ 𝟙 (D.X q)) +
        p.negOnePow • (π P hC hD p q₁ r ≫ P.tensor.map (𝟙 (C.X p) ×ₘ D.d q₁ q)) := by
  have := P.hasMapBifunctor_of_finite hC hD
  ext a b hab
  change a + b = r at hab
  have hι : HomologicalComplex.ιMapBifunctor C D (Functor.curry.obj P.tensor)
      (ComplexShape.down ℤ) a b r hab = ι P hC hD a b r :=
    (HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hab).symm
  rw [hι, ← Category.assoc, ι_d P hC hD (r' := r') hab (sub_add_cancel a 1) (sub_add_cancel b 1)]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  by_cases h1 : a = p₁ ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h1
    have e : a - 1 = p := by omega
    subst e
    rw [ι_π_self P hC hD (p := a - 1) (q := b) (r := r') (by omega),
      ι_π_of_ne P hC hD (p := a) (q := b - 1) (p' := a - 1) (q' := b) (r := r') (by omega),
      ι_π_self_assoc P hC hD (p := a) (q := b) (r := r) hab,
      ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := a - 1) (q' := q₁) (r := r) (by omega)]
    simp
  · by_cases h2 : a = p ∧ b = q₁
    · obtain ⟨rfl, rfl⟩ := h2
      have e : b - 1 = q := by omega
      subst e
      rw [ι_π_of_ne P hC hD (p := a - 1) (q := b) (p' := a) (q' := b - 1) (r := r') (by omega),
        ι_π_self P hC hD (p := a) (q := b - 1) (r := r') (by omega),
        ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := p₁) (q' := b - 1) (r := r) (by omega),
        ι_π_self_assoc P hC hD (p := a) (q := b) (r := r) hab]
      simp
    · rw [ι_π_of_ne P hC hD (p := a - 1) (q := b) (p' := p) (q' := q) (r := r') (by omega),
        ι_π_of_ne P hC hD (p := a) (q := b - 1) (p' := p) (q' := q) (r := r') (by omega),
        ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := p₁) (q' := q) (r := r) h1,
        ι_π_of_ne_assoc P hC hD (p := a) (q := b) (p' := p) (q' := q₁) (r := r) h2]
      simp

end cxProd

private lemma dualHom_comp_assoc' {X Y Z W : B''} (f : X ⟶ Y) (g : Y ⟶ Z) (h : dual X ⟶ W) :
    dualHom g ≫ dualHom f ≫ h = dualHom (f ≫ g) ≫ h := by
  rw [dualHom_comp, Category.assoc]

local notation "ιL" => cxProd.ι P hC hD
local notation "πL" => cxProd.π P hC hD
local notation "ιR" => cxProd.ι P (dualCx_finite hC m) (dualCx_finite hD n)
local notation "πR" => cxProd.π P (dualCx_finite hC m) (dualCx_finite hD n)

private lemma xi_comm (k : ℤ) (hk : m + n = k) (i j : ℤ) (hij : j + 1 = i) :
    xiHom P hC hD m n k i ≫
        (cxProd P (dualCx C m) (dualCx D n) (dualCx_finite hC m) (dualCx_finite hD n)).d i j =
      (dualCx (cxProd P C D hC hD) k).d i j ≫ xiHom P hC hD m n k j := by
  refine cxProd.hom_ext_to P _ _ fun a b hab => ?_
  refine cxProd.dual_hom_ext P hC hD fun x₁ x₂ hx => ?_
  obtain ⟨a', rfl⟩ : ∃ a', x₁ = m - a' := ⟨m - x₁, by ring⟩
  obtain ⟨b', rfl⟩ : ∃ b', x₂ = n - b' := ⟨n - x₂, by ring⟩
  have L : dualHom (πL (m - a') (n - b') (k - i)) ≫ (xiHom P hC hD m n k i ≫
      (cxProd P (dualCx C m) (dualCx D n) (dualCx_finite hC m) (dualCx_finite hD n)).d i j) ≫
        πR a b j =
      sgn m (a + 1) b • (dualHom (ιL (m - (a + 1)) (n - b) (k - i) ≫
          πL (m - a') (n - b') (k - i)) ≫ (P.κ (C.X (m - (a + 1))) (D.X (n - b))).hom ≫
          P.tensor.map ((dualCx C m).d (a + 1) a ×ₘ 𝟙 ((dualCx D n).X b))) +
        a.negOnePow • sgn m a (b + 1) • (dualHom (ιL (m - a) (n - (b + 1)) (k - i) ≫
          πL (m - a') (n - b') (k - i)) ≫ (P.κ (C.X (m - a)) (D.X (n - (b + 1)))).hom ≫
          P.tensor.map (𝟙 ((dualCx C m).X a) ×ₘ (dualCx D n).d (b + 1) b)) := by
    rw [Category.assoc,
      cxProd.d_π P _ _ (p₁ := a + 1) (q₁ := b + 1) hij hab rfl rfl, Preadditive.comp_add,
      Preadditive.comp_add, Linear.comp_units_smul, Linear.comp_units_smul,
      xiHom_π_assoc P hC hD m n (by omega), xiHom_π_assoc P hC hD m n (by omega),
      Linear.units_smul_comp, Linear.units_smul_comp, Linear.comp_units_smul,
      Linear.comp_units_smul, Category.assoc, Category.assoc, dualHom_comp_assoc',
      dualHom_comp_assoc']
  have R : dualHom (πL (m - a') (n - b') (k - i)) ≫
      ((dualCx (cxProd P C D hC hD) k).d i j ≫ xiHom P hC hD m n k j) ≫ πR a b j =
      i.negOnePow • sgn m a b • (dualHom (ιL (m - a) (n - b) (k - j) ≫
        (cxProd P C D hC hD).d (k - j) (k - i) ≫ πL (m - a') (n - b') (k - i)) ≫
        (P.κ (C.X (m - a)) (D.X (n - b))).hom) := by
    rw [Category.assoc, xiHom_π P hC hD m n hab, dualCx_d,
      Linear.units_smul_comp, Linear.comp_units_smul, Linear.comp_units_smul,
      Linear.comp_units_smul, dualHom_comp_assoc', dualHom_comp_assoc']
  rw [L, R]
  obtain rfl : i = j + 1 := hij.symm
  obtain rfl : j = a + b := hab.symm
  by_cases hA : a' = a + 1 ∧ b' = b
  · obtain ⟨h1, h2⟩ := hA
    subst a' b'
    rw [cxProd.ι_π_self P hC hD (p := m - (a + 1)) (q := n - b) (r := k - (a + b + 1))
        (by omega),
      cxProd.ι_π_of_ne P hC hD (p := m - a) (q := n - (b + 1)) (p' := m - (a + 1)) (q' := n - b)
        (r := k - (a + b + 1)) (by omega),
      dualHom_id, dualHom_zero, Category.id_comp, zero_comp, smul_zero, smul_zero, add_zero,
      cxProd.d_π P hC hD (p₁ := m - a) (q₁ := n - b + 1) (by omega) (by omega) (by omega) rfl,
      Preadditive.comp_add, Linear.comp_units_smul,
      cxProd.ι_π_self_assoc P hC hD (p := m - a) (q := n - b) (r := k - (a + b)) (by omega),
      cxProd.ι_π_of_ne_assoc P hC hD (p := m - a) (q := n - b) (p' := m - (a + 1))
        (q' := n - b + 1) (r := k - (a + b)) (by omega),
      zero_comp, smul_zero, add_zero, P.κ_natural, dualHom_id, dualCx_d,
      tensor_units_smul_left, Linear.comp_units_smul, smul_smul, smul_smul]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  by_cases hB : a' = a ∧ b' = b + 1
  · obtain ⟨h1, h2⟩ := hB
    subst a' b'
    rw [cxProd.ι_π_of_ne P hC hD (p := m - (a + 1)) (q := n - b) (p' := m - a)
        (q' := n - (b + 1)) (r := k - (a + b + 1)) (by omega),
      cxProd.ι_π_self P hC hD (p := m - a) (q := n - (b + 1)) (r := k - (a + b + 1))
        (by omega),
      dualHom_id, dualHom_zero, Category.id_comp, zero_comp, smul_zero, zero_add,
      cxProd.d_π P hC hD (p₁ := m - a + 1) (q₁ := n - b) (by omega) (by omega) rfl (by omega),
      Preadditive.comp_add, Linear.comp_units_smul,
      cxProd.ι_π_of_ne_assoc P hC hD (p := m - a) (q := n - b) (p' := m - a + 1)
        (q' := n - (b + 1)) (r := k - (a + b)) (by omega),
      cxProd.ι_π_self_assoc P hC hD (p := m - a) (q := n - b) (r := k - (a + b)) (by omega),
      zero_comp, zero_add, dualHom_units_smul, Linear.units_smul_comp, P.κ_natural, dualHom_id,
      dualCx_d, tensor_units_smul_right, Linear.comp_units_smul]
    simp only [smul_smul]
    congr 1
    simp only [← Int.negOnePow_add]
    rw [Int.negOnePow_eq_iff]
    exact ⟨a, by ring⟩
  · rw [cxProd.ι_π_of_ne P hC hD (p := m - (a + 1)) (q := n - b) (p' := m - a')
        (q' := n - b') (r := k - (a + b + 1)) (by omega),
      cxProd.ι_π_of_ne P hC hD (p := m - a) (q := n - (b + 1)) (p' := m - a')
        (q' := n - b') (r := k - (a + b + 1)) (by omega),
      cxProd.d_π P hC hD (p₁ := m - a' + 1) (q₁ := n - b' + 1) (by omega) (by omega) rfl rfl,
      Preadditive.comp_add, Linear.comp_units_smul,
      cxProd.ι_π_of_ne_assoc P hC hD (p := m - a) (q := n - b) (p' := m - a' + 1)
        (q' := n - b') (r := k - (a + b)) (by omega),
      cxProd.ι_π_of_ne_assoc P hC hD (p := m - a) (q := n - b) (p' := m - a')
        (q' := n - b' + 1) (r := k - (a + b)) (by omega)]
    simp

/-- The degreewise isomorphism `Ξ_r`. -/
private noncomputable def xiIso (k : ℤ) (hk : m + n = k) (r : ℤ) :
    dual ((cxProd P C D hC hD).X (k - r)) ≅
      (cxProd P (dualCx C m) (dualCx D n) (dualCx_finite hC m) (dualCx_finite hD n)).X r where
  hom := xiHom P hC hD m n k r
  inv := xiInv P hC hD m n k r
  hom_inv_id := by
    refine cxProd.dual_hom_ext P hC hD fun x₁ x₂ hx => ?_
    obtain ⟨a, rfl⟩ : ∃ a, x₁ = m - a := ⟨m - x₁, by ring⟩
    obtain ⟨b, rfl⟩ : ∃ b, x₂ = n - b := ⟨n - x₂, by ring⟩
    rw [← Category.assoc, dualπ_xiHom P hC hD m n hk (by omega), Linear.units_smul_comp,
      Category.assoc, ι_xiInv P hC hD m n (by omega), Linear.comp_units_smul, smul_smul,
      sgn_mul_self, one_smul, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine cxProd.hom_ext_to P _ _ fun a b h => ?_
    rw [Category.assoc, xiHom_π P hC hD m n h, Linear.comp_units_smul, ← Category.assoc,
      xiInv_dualι P hC hD m n hk h, Linear.units_smul_comp, smul_smul, sgn_mul_self, one_smul,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- **Dual of a tensor product.** The isomorphism of complexes
`Ξ : (C ⊗ D)^{k-*} ≅ C^{m-*} ⊗ D^{n-*}` (`k = m + n`), equal to `(-1)^{b(a+m)} κ` from the dual of
the summand `C_{m-a} ⊠ D_{n-b}` to the summand `C_{m-a}^* ⊠ D_{n-b}^*` in position `(a, b)`. -/
noncomputable def prodDualIso (k : ℤ) (hk : m + n = k) :
    dualCx (cxProd P C D hC hD) k ≅
      cxProd P (dualCx C m) (dualCx D n) (dualCx_finite hC m) (dualCx_finite hD n) :=
  HomologicalComplex.Hom.isoOfComponents (xiIso P hC hD m n k hk) fun i j hij =>
    xi_comm P hC hD m n k hk i j hij

/-- The block of `Ξ` from the dual of the summand `C_{m-a} ⊠ D_{n-b}`: `(-1)^{b(a+m)} κ` followed by
the inclusion of the summand `C_{m-a}^* ⊠ D_{n-b}^*` in position `(a, b)`. -/
@[reassoc]
lemma prodDualIso_hom_block (k : ℤ) (hk : m + n = k) {a b r : ℤ} (h : a + b = r) :
    dualHom (cxProd.π P hC hD (m - a) (n - b) (k - r)) ≫ (prodDualIso P hC hD m n k hk).hom.f r =
      (b * (a + m)).negOnePow • ((P.κ (C.X (m - a)) (D.X (n - b))).hom ≫
        cxProd.ι P (dualCx_finite hC m) (dualCx_finite hD n) a b r) :=
  dualπ_xiHom P hC hD m n hk h

end HSP
