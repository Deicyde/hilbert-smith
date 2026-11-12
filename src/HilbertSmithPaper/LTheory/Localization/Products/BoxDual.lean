import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BoxProduct
import HilbertSmithPaper.LTheory.Localization.Products.DualityPairing
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDiag

/-!
# Duals of box products

For `N = (M, e)` in `Kar B` and `V` in `C_ℤ(ℚ)`, the isomorphism `κ : (N ⊠ V)^* ≅ N^* ⊠ V^*` has
propagation `0`; in position `n` it is the canonical isomorphism
`c : (M^{⊕ d_n})^* ≅ (M^*)^{⊕ d_n}` whose components are the duals of the summand inclusions
(followed by the idempotent `e^*` on each summand, which `c` commutes with). With it, the box
product is a duality pairing `Kar B × C_ℤ(ℚ) → Kar C_ℤ(B)`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace BoxDual

private lemma dualHom_sum {X Y : B} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    dualHom (∑ i ∈ s, f i) = ∑ i ∈ s, dualHom (f i) :=
  map_sum (AddMonoidHom.mk' (dualHom (M := X) (N := Y)) dualHom_add) f s

/-- Maps out of the dual of a biproduct agree when they agree on the dual of every projection. -/
private lemma dual_ext {d : ℕ} {X Z : B} {φ ψ : dual (⨁ fun _ : Fin d => X) ⟶ Z}
    (h : ∀ i, dualHom (biproduct.π (fun _ : Fin d => X) i) ≫ φ =
      dualHom (biproduct.π (fun _ : Fin d => X) i) ≫ ψ) : φ = ψ := by
  have h1 : 𝟙 (dual (⨁ fun _ : Fin d => X)) = ∑ i, dualHom (biproduct.ι (fun _ : Fin d => X) i) ≫
      dualHom (biproduct.π (fun _ : Fin d => X) i) := by
    rw [← dualHom_id, ← biproduct.total, dualHom_sum]
    simp only [dualHom_comp]
  rw [← Category.id_comp φ, ← Category.id_comp ψ, h1, Preadditive.sum_comp, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [Category.assoc, Category.assoc, h i]

/-- The canonical map `(X^{⊕ d})^* ⟶ (X^*)^{⊕ d}`, with components the duals of the inclusions. -/
private noncomputable def can (X : B) (d : ℕ) :
    dual (⨁ fun _ : Fin d => X) ⟶ ⨁ fun _ : Fin d => dual X :=
  biproduct.lift fun i => dualHom (biproduct.ι (fun _ : Fin d => X) i)

/-- Its inverse, with components the duals of the projections. -/
private noncomputable def canInv (X : B) (d : ℕ) :
    (⨁ fun _ : Fin d => dual X) ⟶ dual (⨁ fun _ : Fin d => X) :=
  biproduct.desc fun i => dualHom (biproduct.π (fun _ : Fin d => X) i)

@[reassoc (attr := simp)]
private lemma can_π (X : B) (d : ℕ) (i : Fin d) :
    can X d ≫ biproduct.π _ i = dualHom (biproduct.ι (fun _ : Fin d => X) i) :=
  biproduct.lift_π _ _

@[reassoc (attr := simp)]
private lemma ι_canInv (X : B) (d : ℕ) (i : Fin d) :
    biproduct.ι (fun _ : Fin d => dual X) i ≫ canInv X d =
      dualHom (biproduct.π (fun _ : Fin d => X) i) :=
  biproduct.ι_desc _ _

@[reassoc (attr := simp)]
private lemma dualπ_can (X : B) (d : ℕ) (i : Fin d) :
    dualHom (biproduct.π (fun _ : Fin d => X) i) ≫ can X d =
      biproduct.ι (fun _ : Fin d => dual X) i := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, can_π, ← dualHom_comp, biproduct.ι_π, biproduct.ι_π]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

@[reassoc (attr := simp)]
private lemma canInv_can (X : B) (d : ℕ) : canInv X d ≫ can X d = 𝟙 _ :=
  biproduct.hom_ext' _ _ fun i => by rw [ι_canInv_assoc, dualπ_can, Category.comp_id]

private lemma can_map_canInv (X : B) (d : ℕ) (e : X ⟶ X) :
    can X d ≫ biproduct.map (fun _ => dualHom e) ≫ canInv X d =
      dualHom (biproduct.map fun _ : Fin d => e) :=
  dual_ext fun i => by
    rw [dualπ_can_assoc, biproduct.ι_map_assoc, ι_canInv, ← dualHom_comp, ← dualHom_comp,
      biproduct.map_π]

@[reassoc]
private lemma dualHom_map_can (X : B) (d : ℕ) (e : X ⟶ X) :
    dualHom (biproduct.map fun _ : Fin d => e) ≫ can X d =
      can X d ≫ biproduct.map fun _ => dualHom e :=
  biproduct.hom_ext _ _ fun j => by
    rw [Category.assoc, can_π, ← dualHom_comp, biproduct.ι_map, Category.assoc,
      biproduct.map_π, can_π_assoc, dualHom_comp]

omit [Linear ℚ B] [DualCat B] in
@[reassoc]
private lemma map_map {d : ℕ} {X : B} (a b : X ⟶ X) :
    (biproduct.map fun _ : Fin d => a) ≫ (biproduct.map fun _ : Fin d => b) =
      biproduct.map fun _ : Fin d => a ≫ b :=
  biproduct.hom_ext _ _ fun j => by simp

omit [DualCat B] in
/-- The idempotent of `N ⊠ V`, in position `n`. -/
private lemma obj_p (N : Karoubi B) (V : Bounded FreeQ) :
    (Box.obj N V).p = Bounded.diag fun n => biproduct.map fun _ : Fin (V.X n).dim => N.p := rfl

/-- `κ : (N ⊠ V)^* ⟶ N^* ⊠ V^*`, in position `n` the canonical map followed by `e^*`. -/
private noncomputable def kappaHom (N : Karoubi B) (V : Bounded FreeQ) :
    dual (Box.obj N V) ⟶ Box.obj (dual N) (dual V) where
  f := Bounded.diag (M := dual (Box.obj N V).X) (N := (Box.obj (dual N) (dual V)).X)
    fun n => can N.X (V.X n).dim ≫ biproduct.map fun _ => dualHom N.p
  comm := by
    rw [Karoubi.dual_p, obj_p, Bounded.dualHom_diag_eq, obj_p, Bounded.diag_comp_diag,
      Bounded.diag_comp_diag]
    congr 1
    funext n
    change dualHom (biproduct.map fun _ : Fin (V.X n).dim => N.p) ≫
      (can N.X (V.X n).dim ≫ biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫
        (biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) =
      can N.X (V.X n).dim ≫ biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p
    simp only [Category.assoc]
    rw [dualHom_map_can_assoc, map_map, map_map, ← dualHom_comp, ← dualHom_comp, N.idem,
      N.idem]

/-- `κ⁻¹ : N^* ⊠ V^* ⟶ (N ⊠ V)^*`. -/
private noncomputable def kappaInv (N : Karoubi B) (V : Bounded FreeQ) :
    Box.obj (dual N) (dual V) ⟶ dual (Box.obj N V) where
  f := Bounded.diag (M := (Box.obj (dual N) (dual V)).X) (N := dual (Box.obj N V).X)
    fun n => (biproduct.map fun _ => dualHom N.p) ≫ canInv N.X (V.X n).dim
  comm := by
    simp only [Karoubi.dual_p, Bounded.dualHom_diag_eq, Bounded.diag_comp_diag]
    congr 1
    funext n
    change (biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫
      ((biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫ canInv N.X (V.X n).dim) ≫
        dualHom (biproduct.map fun _ : Fin (V.X n).dim => N.p) =
      (biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫ canInv N.X (V.X n).dim
    rw [← can_map_canInv]
    simp only [Category.assoc]
    rw [canInv_can_assoc, map_map_assoc, map_map_assoc, ← dualHom_comp, N.idem,
      ← dualHom_comp, N.idem]

/-- The isomorphism `κ : (N ⊠ V)^* ≅ N^* ⊠ V^*`. -/
private noncomputable def kappa (N : Karoubi B) (V : Bounded FreeQ) :
    dual (Box.obj N V) ≅ Box.obj (dual N) (dual V) where
  hom := kappaHom N V
  inv := kappaInv N V
  hom_inv_id := by
    refine Karoubi.hom_ext _ _ ?_
    rw [Karoubi.comp_f, Karoubi.id_f, Karoubi.dual_p, obj_p, Bounded.dualHom_diag_eq]
    change Bounded.diag _ ≫ Bounded.diag _ = _
    rw [Bounded.diag_comp_diag]
    congr 1
    funext n
    change (can N.X (V.X n).dim ≫ biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫
      ((biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫ canInv N.X (V.X n).dim) =
      dualHom (biproduct.map fun _ : Fin (V.X n).dim => N.p)
    rw [Category.assoc, map_map_assoc, ← dualHom_comp, N.idem, can_map_canInv]
  inv_hom_id := by
    refine Karoubi.hom_ext _ _ ?_
    rw [Karoubi.comp_f, Karoubi.id_f, obj_p]
    change Bounded.diag _ ≫ Bounded.diag _ = _
    rw [Bounded.diag_comp_diag]
    congr 1
    funext n
    change ((biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) ≫ canInv N.X (V.X n).dim) ≫
      (can N.X (V.X n).dim ≫ biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p) =
      biproduct.map fun _ : Fin (V.X n).dim => dualHom N.p
    rw [Category.assoc, canInv_can_assoc, map_map, ← dualHom_comp, N.idem]

end BoxDual

omit [HasFiniteBiproducts B] [DualCat B] in
private lemma comp_eqToHom_apply {M N N' : Bounded B} (f : M ⟶ N) (h : N = N') (m n : ℤ) :
    (f ≫ eqToHom h).1 m n = f.1 m n ≫ eqToHom (congrArg (fun K : Bounded B => K.X m) h) := by
  subst h
  simp

omit [Linear ℚ B] [DualCat B] in
@[reassoc]
private lemma ι_eqToHom_biproduct {d : ℕ} {X Y : B} (h : X = Y) (i : Fin d) :
    biproduct.ι (fun _ : Fin d => X) i ≫ eqToHom (by rw [h]) =
      eqToHom h ≫ biproduct.ι (fun _ : Fin d => Y) i := by
  subst h; simp

omit [Linear ℚ B] [DualCat B] in
private lemma biprod_ext' {J K : Type} [Fintype J] [Fintype K] {f : J → B} {g : K → B}
    {φ ψ : ⨁ f ⟶ ⨁ g}
    (h : ∀ j k, biproduct.ι f j ≫ φ ≫ biproduct.π g k = biproduct.ι f j ≫ ψ ≫ biproduct.π g k) :
    φ = ψ := by
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  simpa only [Category.assoc] using h j k

section Bilinear

variable {N N' : Karoubi B} {V V' : Bounded FreeQ}

omit [DualCat B] in
private lemma map_add_left (f f' : N ⟶ N') (g : V ⟶ V') :
    (boxProduct (B := B)).map ((f + f') ×ₘ g) =
      (boxProduct (B := B)).map (f ×ₘ g) + (boxProduct (B := B)).map (f' ×ₘ g) := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => biprod_ext' fun i i' => ?_)
  change _ ≫ Box.F (f + f') g m n ≫ _ = _ ≫ (Box.F f g m n + Box.F f' g m n) ≫ _
  rw [Preadditive.add_comp, Preadditive.comp_add, Box.F_entry, Box.F_entry, Box.F_entry]
  exact smul_add _ _ _

omit [DualCat B] in
private lemma map_add_right (f : N ⟶ N') (g g' : V ⟶ V') :
    (boxProduct (B := B)).map (f ×ₘ (g + g')) =
      (boxProduct (B := B)).map (f ×ₘ g) + (boxProduct (B := B)).map (f ×ₘ g') := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => biprod_ext' fun i i' => ?_)
  change _ ≫ Box.F f (g + g') m n ≫ _ = _ ≫ (Box.F f g m n + Box.F f g' m n) ≫ _
  rw [Preadditive.add_comp, Preadditive.comp_add, Box.F_entry, Box.F_entry, Box.F_entry,
    Bounded.add_apply, FreeQ.add_toMatrix, Matrix.add_apply, add_smul]

omit [DualCat B] in
private lemma map_smul_left (c : ℚ) (f : N ⟶ N') (g : V ⟶ V') :
    (boxProduct (B := B)).map ((c • f) ×ₘ g) = c • (boxProduct (B := B)).map (f ×ₘ g) := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => biprod_ext' fun i i' => ?_)
  change _ ≫ Box.F (c • f) g m n ≫ _ = _ ≫ (c • Box.F f g m n) ≫ _
  rw [Linear.smul_comp, Linear.comp_smul, Box.F_entry, Box.F_entry, Karoubi.smul_f]
  exact smul_comm _ _ _

omit [DualCat B] in
private lemma map_smul_right (c : ℚ) (f : N ⟶ N') (g : V ⟶ V') :
    (boxProduct (B := B)).map (f ×ₘ (c • g)) = c • (boxProduct (B := B)).map (f ×ₘ g) := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => biprod_ext' fun i i' => ?_)
  change _ ≫ Box.F f (c • g) m n ≫ _ = _ ≫ (c • Box.F f g m n) ≫ _
  rw [Linear.smul_comp, Linear.comp_smul, Box.F_entry, Box.F_entry, Bounded.smul_apply,
    FreeQ.smul_toMatrix, Matrix.smul_apply, smul_eq_mul, mul_smul]

end Bilinear

/-- **Duals of box products.** With `κ`, the box product is a duality pairing
`Kar B × C_ℤ(ℚ) → Kar C_ℤ(B)`. -/
noncomputable def boxPairing :
    DualityPairing (Karoubi B) (Bounded FreeQ) (Karoubi (Bounded B)) where
  tensor := boxProduct
  map_add_left f f' g := map_add_left f f' g
  map_add_right f g g' := map_add_right f g g'
  map_smul_left c f g := map_smul_left c f g
  map_smul_right c f g := map_smul_right c f g
  κ N V := BoxDual.kappa N V
  κ_natural {N N' V V'} f g := by
    refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun a b => ?_)
    change Bounded.compF (M := dual (Box.obj N' V').X) (N := dual (Box.obj N V).X)
        (P := (Box.obj (dual N) (dual V)).X) (fun a b => dualHom (Box.F f g b a))
        (Bounded.diagF (M := dual (Box.obj N V).X) (N := (Box.obj (dual N) (dual V)).X)
          fun n => BoxDual.can N.X (V.X n).dim ≫ biproduct.map fun _ => dualHom N.p) a b =
      Bounded.compF
        (Bounded.diagF (M := dual (Box.obj N' V').X) (N := (Box.obj (dual N') (dual V')).X)
          fun n => BoxDual.can N'.X (V'.X n).dim ≫ biproduct.map fun _ => dualHom N'.p)
        (Box.F (dualHom f) (dualHom g)) a b
    rw [Bounded.compF_diagF, Bounded.diagF_compF]
    change dualHom (Box.F f g b a) ≫
        (BoxDual.can N.X (V.X a).dim ≫ biproduct.map fun _ : Fin (V.X a).dim => dualHom N.p) =
      (BoxDual.can N'.X (V'.X b).dim ≫ biproduct.map fun _ : Fin (V'.X b).dim => dualHom N'.p) ≫
        Box.F (dualHom f) (dualHom g) a b
    refine BoxDual.dual_ext fun i' => biproduct.hom_ext _ _ fun i => ?_
    simp only [Category.assoc, biproduct.map_π, BoxDual.can_π_assoc]
    rw [← dualHom_comp, ← dualHom_comp, ← dualHom_comp, BoxDual.dualπ_can_assoc,
      biproduct.ι_map_assoc]
    simp only [Category.assoc, Box.F_entry, Linear.comp_smul, Karoubi.p_comp, dualHom_smul]
    erw [Box.F_entry (dualHom f) (dualHom g) a b i' i]
    rw [Linear.comp_smul]
    change _ = FreeQ.toMatrix (g.1 b a) i' i • (dualHom N'.p ≫ dualHom f.f)
    rw [← dualHom_comp, Karoubi.comp_p]
  κ_dual N V := by
    refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun a b => ?_)
    rw [Karoubi.comp_f, Karoubi.eqToHom_f, ← Category.assoc, Karoubi.comp_p,
      comp_eqToHom_apply]
    change dualHom (Bounded.diagF (M := dual (Box.obj N V).X) (N := (Box.obj (dual N) (dual V)).X)
        (fun n => BoxDual.can N.X (V.X n).dim ≫ biproduct.map fun _ => dualHom N.p) b a) =
      Bounded.diagF (M := dual (Box.obj (dual N) (dual V)).X)
        (N := (Box.obj (dual (dual N)) (dual (dual V))).X)
        (fun n => BoxDual.can (dual N.X) (V.X n).dim ≫
          biproduct.map fun _ => dualHom (dualHom N.p)) a b ≫
        eqToHom (show (⨁ fun _ : Fin (V.X a).dim => dual (dual N.X)) =
          dual (dual (⨁ fun _ : Fin (V.X a).dim => N.X)) by rw [dual_dual, dual_dual])
    by_cases h : a = b
    · subst h
      rw [Bounded.diagF_self, Bounded.diagF_self]
      refine BoxDual.dual_ext fun i => ?_
      change dualHom (biproduct.π (fun _ : Fin (V.X a).dim => dual N.X) i) ≫
          dualHom (BoxDual.can N.X (V.X a).dim ≫ biproduct.map fun _ => dualHom N.p) =
        dualHom (biproduct.π (fun _ : Fin (V.X a).dim => dual N.X) i) ≫
          (BoxDual.can (dual N.X) (V.X a).dim ≫
            biproduct.map fun _ => dualHom (dualHom N.p)) ≫ eqToHom _
      simp only [Category.assoc]
      rw [← dualHom_comp, Category.assoc, biproduct.map_π, BoxDual.can_π_assoc, ← dualHom_comp,
        BoxDual.dualπ_can_assoc, biproduct.ι_map_assoc, dualHom_dualHom, dualHom_dualHom]
      simp only [Category.assoc]
      rw [← ι_eqToHom_biproduct_assoc (dual_dual N.X).symm, eqToHom_trans]
    · rw [Bounded.diagF_ne _ (Ne.symm h), Bounded.diagF_ne _ h, dualHom_zero, zero_comp]

end HSP
