import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedSub

/-!
# The bounded subcategory is closed under sums and duals

If `U ⊂ A` is a full additive subcategory closed under duality, so is `C_ℤ(U) ⊂ C_ℤ(A)`: the
constant family at a zero object of `U` is a zero object, sums are assembled from degreewise
bilimit bicones in `U`, and `(M^*)_n = (M_n)^*`.

## Encoding

`Bounded.isDualAdditive_sub U` (the declaration of the article) is an instance of
`IsDualAdditive (Bounded.sub U)`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma diag_id_eq (M : Bounded A) : (diag fun n => 𝟙 (M.X n)) = 𝟙 M := rfl

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
private lemma bilimit_total {X Y : A} {c : BinaryBicone X Y} (hc : c.IsBilimit) :
    c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt := by
  refine BinaryFan.IsLimit.hom_ext hc.isLimit ?_ ?_ <;> simp

instance isDualAdditive_sub (U : ObjectProperty A) [IsDualAdditive U] :
    IsDualAdditive (sub U) where
  exists_zero := by
    obtain ⟨Z, hZ, hZ0⟩ := IsDualAdditive.exists_zero (U := U)
    refine ⟨⟨fun _ => Z⟩, fun _ => hZ, ?_⟩
    rw [IsZero.iff_id_eq_zero, ← diag_id_eq]
    rw [show (fun _ : ℤ => 𝟙 Z) = fun _ => 0 from funext fun _ => hZ0.eq_of_src _ _]
    exact diag_zero
  exists_biprod {V W} hV hW := by
    choose c hc hcU using fun n => IsDualAdditive.exists_biprod (hV n) (hW n)
    let P : Bounded A := ⟨fun n => (c n).pt⟩
    let b : BinaryBicone V W :=
      { pt := P
        fst := diag (M := P) (N := V) fun n => (c n).fst
        snd := diag (M := P) (N := W) fun n => (c n).snd
        inl := diag (M := V) (N := P) fun n => (c n).inl
        inr := diag (M := W) (N := P) fun n => (c n).inr
        inl_fst := by rw [diag_comp_diag]; simp only [BinaryBicone.inl_fst]; rfl
        inl_snd := by rw [diag_comp_diag]; simp only [BinaryBicone.inl_snd]; exact diag_zero
        inr_fst := by rw [diag_comp_diag]; simp only [BinaryBicone.inr_fst]; exact diag_zero
        inr_snd := by rw [diag_comp_diag]; simp only [BinaryBicone.inr_snd]; rfl }
    refine ⟨b, ⟨isBinaryBilimitOfTotal b ?_⟩, fun n => hcU n⟩
    change (diag (M := P) (N := V) fun n => (c n).fst) ≫
        (diag (M := V) (N := P) fun n => (c n).inl) +
      (diag (M := P) (N := W) fun n => (c n).snd) ≫
        (diag (M := W) (N := P) fun n => (c n).inr) = 𝟙 P
    rw [diag_comp_diag, diag_comp_diag]
    refine hom_ext fun m n => ?_
    rw [add_apply, diag_apply, diag_apply, ← diag_id_eq, diag_apply]
    by_cases h : m = n
    · subst h
      simp only [diagF_self]
      exact bilimit_total (hc m).some
    · simp only [diagF_ne _ h, add_zero]
  dual_mem hV n := IsDualAdditive.dual_mem (hV n)

end Bounded

end HSP

end
