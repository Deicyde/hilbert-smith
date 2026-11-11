import Mathlib
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedCategory

/-!
# Box product with a bounded vector space

For a ℚ-linear additive category `B` and the category `ℚ` of based vector spaces, the box product
is the ℚ-bilinear functor `⊠ : Kar B × C_ℤ(ℚ) ⥤ Kar C_ℤ(B)`. For `N = (M, e)` and
`V = (ℚ^{d_n})_n`, `N ⊠ V` has `M^{⊕ d_n}` in position `n` (the biproduct of `d_n` copies of `M`)
and the idempotent `e` on each summand. For `f : N ⟶ N'` and `g : V ⟶ V'`, the component
`(f ⊠ g)_{mn}` is the block matrix whose `(i, i')` entry (from summand `i` to summand `i'`) is
`(g_{mn})_{i'i} f`; it has the propagation of `g`. For `B = C_{ℤ^j} A` the target is
`Kar C_{ℤ^{j+1}} A`, the new coordinate being the outermost one (`BoundedPow A (j+1)` is
`Bounded (BoundedPow A j)` by definition).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open scoped CategoryTheory.Prod

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]

namespace Box

omit [Linear ℚ B] in
private lemma biprod_ext {J K : Type} [Fintype J] [Fintype K] {f : J → B} {g : K → B}
    {φ ψ : ⨁ f ⟶ ⨁ g}
    (h : ∀ j k, biproduct.ι f j ≫ φ ≫ biproduct.π g k = biproduct.ι f j ≫ ψ ≫ biproduct.π g k) :
    φ = ψ := by
  refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
  simpa only [Category.assoc] using h j k

/-- The object `N ⊠ V`: `M^{⊕ d_n}` in position `n`, with `e` on each summand. -/
noncomputable abbrev obj (N : Karoubi B) (V : Bounded FreeQ) : Karoubi (Bounded B) where
  X := ⟨fun n => ⨁ fun _ : Fin (V.X n).dim => N.X⟩
  p := Bounded.diag fun n => biproduct.map fun _ => N.p
  idem := by
    rw [Bounded.diag_comp_diag]
    congr 1
    funext n
    exact biprod_ext fun i i' => by simp

/-- The components `(f ⊠ g)_{mn}`: block matrices with entries `(g_{mn})_{i'i} f`. -/
noncomputable def F {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V')
    (m n : ℤ) : (obj N V).X.X n ⟶ (obj N' V').X.X m :=
  biproduct.matrix fun (i : Fin (V.X n).dim) (i' : Fin (V'.X m).dim) =>
    FreeQ.toMatrix (g.1 m n) i' i • f.f

@[reassoc]
lemma F_entry {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V') (m n : ℤ)
    (i : Fin (V.X n).dim) (i' : Fin (V'.X m).dim) :
    biproduct.ι (fun _ : Fin (V.X n).dim => N.X) i ≫ F f g m n ≫
        biproduct.π (fun _ : Fin (V'.X m).dim => N'.X) i' =
      FreeQ.toMatrix (g.1 m n) i' i • f.f :=
  biproduct.matrix_components _ _ _

private lemma F_mem {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V') :
    F f g ∈ Bounded.homSub (obj N V).X (obj N' V').X := by
  obtain ⟨r, hr⟩ := g.2
  refine ⟨r, fun m n h => biprod_ext fun i i' => ?_⟩
  rw [F_entry, hr m n h]
  simp

/-- The morphism `f ⊠ g : N ⊠ V ⟶ N' ⊠ V'`. -/
noncomputable def map {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V') :
    obj N V ⟶ obj N' V' where
  f := ⟨F f g, F_mem f g⟩
  comm := by
    refine Bounded.hom_ext fun m n => ?_
    change Bounded.compF (Bounded.diagF (M := (obj N V).X) (N := (obj N V).X)
        fun n => biproduct.map fun _ => N.p)
      (Bounded.compF (F f g) (Bounded.diagF (M := (obj N' V').X) (N := (obj N' V').X)
        fun n => biproduct.map fun _ => N'.p)) m n = F f g m n
    rw [Bounded.diagF_compF, Bounded.compF_diagF]
    refine biprod_ext fun i i' => ?_
    simp only [Category.assoc, biproduct.ι_map_assoc, biproduct.map_π, F_entry_assoc, F_entry,
      Linear.comp_smul, Linear.smul_comp, f.comm]

lemma F_eq_zero {N N' : Karoubi B} {V V' : Bounded FreeQ} (f : N ⟶ N') (g : V ⟶ V') {m n : ℤ}
    (h : g.1 m n = 0) : F f g m n = 0 :=
  biprod_ext fun i i' => by rw [F_entry, h]; simp

omit [Linear ℚ B] in
private lemma entry_comp {J K L : Type} [Fintype J] [Fintype K] [Fintype L] {f : J → B}
    {g : K → B} {h : L → B} (φ : ⨁ f ⟶ ⨁ g) (ψ : ⨁ g ⟶ ⨁ h) (j : J) (l : L) :
    biproduct.ι f j ≫ φ ≫ ψ ≫ biproduct.π h l =
      ∑ k, (biproduct.ι f j ≫ φ ≫ biproduct.π g k) ≫ (biproduct.ι g k ≫ ψ ≫ biproduct.π h l) := by
  conv_lhs => rw [← Category.id_comp ψ, ← biproduct.total]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]

lemma toMatrix_sum {X Y : FreeQ} {ι : Type*} (s : Finset ι) (x : ι → (X ⟶ Y)) :
    FreeQ.toMatrix (∑ m ∈ s, x m) = ∑ m ∈ s, FreeQ.toMatrix (x m) :=
  map_sum (AddMonoidHom.mk' (fun f : X ⟶ Y => FreeQ.toMatrix f) FreeQ.add_toMatrix) x s

private lemma window {V V' : Bounded FreeQ} (g : V ⟶ V') (n : ℤ) :
    ∃ s : Finset ℤ, ∀ m ∉ s, g.1 m n = 0 := by
  obtain ⟨r, hr⟩ := g.2
  exact ⟨Finset.Icc (n - r) (n + r), fun m hm => hr m n (by
    rw [Finset.mem_Icc] at hm
    rw [lt_abs]
    omega)⟩

end Box

/-- **Box product with a bounded vector space.** The functor
`⊠ : Kar B × C_ℤ(ℚ) ⥤ Kar C_ℤ(B)`, `(N, V) ↦ N ⊠ V`, `(f, g) ↦ f ⊠ g`. -/
noncomputable def boxProduct : Karoubi B × Bounded FreeQ ⥤ Karoubi (Bounded B) where
  obj P := Box.obj P.1 P.2
  map f := Box.map f.1 f.2
  map_id P := by
    refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => ?_)
    change Box.F (𝟙 P.1) (𝟙 P.2) m n = Bounded.diagF (M := (Box.obj P.1 P.2).X)
      (N := (Box.obj P.1 P.2).X) (fun n => biproduct.map fun _ => P.1.p) m n
    by_cases h : m = n
    · subst h
      rw [Bounded.diagF_self]
      refine Box.biprod_ext fun i i' => ?_
      rw [Box.F_entry, biproduct.ι_map_assoc, biproduct.ι_π]
      have h1 : (𝟙 P.2 : P.2 ⟶ P.2).1 m m = 𝟙 (P.2.X m) :=
        Bounded.diagF_self (M := P.2) (N := P.2) (fun n => 𝟙 (P.2.X n)) m
      rw [h1, FreeQ.id_toMatrix, Matrix.one_apply, Karoubi.id_f]
      by_cases hi : i = i'
      · subst hi; simp
      · simp [hi, Ne.symm hi]
    · rw [Bounded.diagF_ne _ h, Box.F_eq_zero _ _
        (Bounded.diagF_ne (M := P.2) (N := P.2) (fun n => 𝟙 (P.2.X n)) h)]
  map_comp {P Q R} f g := by
    refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun l n => ?_)
    change Box.F (f.1 ≫ g.1) (f.2 ≫ g.2) l n = Bounded.compF (Box.F f.1 f.2) (Box.F g.1 g.2) l n
    obtain ⟨s, hs⟩ := Box.window f.2 n
    rw [Bounded.compF_eq_sum _ _ l n s fun m hm => by rw [Box.F_eq_zero _ _ (hs m hm), zero_comp]]
    refine Box.biprod_ext fun i i'' => ?_
    have hc : (f.2 ≫ g.2).1 l n = ∑ m ∈ s, f.2.1 m n ≫ g.2.1 l m :=
      Bounded.compF_eq_sum _ _ l n s fun m hm => by rw [hs m hm, zero_comp]
    rw [Box.F_entry, hc, Box.toMatrix_sum, Matrix.sum_apply i'' i s, Finset.sum_smul,
      Preadditive.sum_comp, Preadditive.comp_sum, Karoubi.comp_f]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Category.assoc, Box.entry_comp, FreeQ.comp_toMatrix, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Box.F_entry, Box.F_entry, Linear.smul_comp, Linear.comp_smul, smul_smul]
    rw [mul_comm]

namespace boxProduct

variable {N N' : Karoubi B} {V V' : Bounded FreeQ}

lemma map_add_left (f f' : N ⟶ N') (g : V ⟶ V') :
    (boxProduct (B := B)).map ((f + f') ×ₘ g) =
      (boxProduct (B := B)).map (f ×ₘ g) + (boxProduct (B := B)).map (f' ×ₘ g) := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => Box.biprod_ext fun i i' => ?_)
  change _ ≫ Box.F (f + f') g m n ≫ _ = _ ≫ (Box.F f g m n + Box.F f' g m n) ≫ _
  rw [Preadditive.add_comp, Preadditive.comp_add, Box.F_entry, Box.F_entry, Box.F_entry]
  exact smul_add _ _ _

lemma map_add_right (f : N ⟶ N') (g g' : V ⟶ V') :
    (boxProduct (B := B)).map (f ×ₘ (g + g')) =
      (boxProduct (B := B)).map (f ×ₘ g) + (boxProduct (B := B)).map (f ×ₘ g') := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => Box.biprod_ext fun i i' => ?_)
  change _ ≫ Box.F f (g + g') m n ≫ _ = _ ≫ (Box.F f g m n + Box.F f g' m n) ≫ _
  rw [Preadditive.add_comp, Preadditive.comp_add, Box.F_entry, Box.F_entry, Box.F_entry,
    Bounded.add_apply, FreeQ.add_toMatrix, Matrix.add_apply, add_smul]

lemma map_smul_left (c : ℚ) (f : N ⟶ N') (g : V ⟶ V') :
    (boxProduct (B := B)).map ((c • f) ×ₘ g) = c • (boxProduct (B := B)).map (f ×ₘ g) := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => Box.biprod_ext fun i i' => ?_)
  change _ ≫ Box.F (c • f) g m n ≫ _ = _ ≫ (c • Box.F f g m n) ≫ _
  rw [Linear.smul_comp, Linear.comp_smul, Box.F_entry, Box.F_entry, Karoubi.smul_f]
  exact smul_comm _ _ _

lemma map_smul_right (c : ℚ) (f : N ⟶ N') (g : V ⟶ V') :
    (boxProduct (B := B)).map (f ×ₘ (c • g)) = c • (boxProduct (B := B)).map (f ×ₘ g) := by
  refine Karoubi.hom_ext _ _ (Bounded.hom_ext fun m n => Box.biprod_ext fun i i' => ?_)
  change _ ≫ Box.F f (c • g) m n ≫ _ = _ ≫ (c • Box.F f g m n) ≫ _
  rw [Linear.smul_comp, Linear.comp_smul, Box.F_entry, Box.F_entry, Bounded.smul_apply,
    FreeQ.smul_toMatrix, Matrix.smul_apply, smul_eq_mul, mul_smul]

end boxProduct

end HSP
