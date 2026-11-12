import HilbertSmithPaper.LTheory.Base.Complexes.DualComplex
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.DualMapIso

/-!
# Duals of homotopy equivalences

If `f : C ⟶ D` is a chain homotopy equivalence of complexes in a duality category, then for every
`n` the dual `f^{n-*} : D^{n-*} ⟶ C^{n-*}` is one, with homotopy inverse `g^{n-*}`. A homotopy
`H` with `f - g = dH + Hd` dualizes to `K_r = (-1)^{r+1} (H_{n-r-1})^*`, with
`f^{n-*} - g^{n-*} = dK + Kd` on the dual complexes, whose differential is `(-1)^r d^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace dualCx

private lemma map_sub {C D : ChainComplex B ℤ} (f g : C ⟶ D) (n : ℤ) :
    dualCx.map (f - g) n = dualCx.map f n - dualCx.map g n := by
  ext r
  simp

/-- The dual of a homotopy: `K_r = (-1)^{r+1} (H_{n-r-1})^*`. -/
private noncomputable def mapHomotopy {C D : ChainComplex B ℤ} {f g : C ⟶ D} (H : Homotopy f g)
    (n : ℤ) : Homotopy (dualCx.map f n) (dualCx.map g n) := by
  refine Homotopy.equivSubZero.symm ((Homotopy.ofEq ?_).trans (Homotopy.nullHomotopy'
    (fun i j _ => (i + 1).negOnePow • dualHom (H.hom (n - j) (n - i)))))
  ext k
  rw [Homotopy.nullHomotopicMap'_f (k₂ := k + 1) (k₀ := k - 1) (by simp) (by simp),
    HomologicalComplex.sub_f_apply]
  have hc := H.comm (n - k)
  rw [dNext_eq H.hom (i' := n - (k + 1)) (by simp only [ComplexShape.down_Rel]; omega),
    prevD_eq H.hom (j' := n - (k - 1)) (by simp only [ComplexShape.down_Rel]; omega)] at hc
  change dualHom (f.f (n - k)) - dualHom (g.f (n - k)) = _
  rw [← dualHom_sub, hc, add_sub_cancel_right]
  simp only [sub_add_cancel]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
    one_smul, dualHom_add, dualHom_comp]
  rw [add_comm]

/-- The dual `f^{n-*} : D^{n-*} ⟶ C^{n-*}` of a chain homotopy equivalence `f : C ⟶ D` is a chain
homotopy equivalence, with homotopy inverse the dual of the inverse of `f`. -/
noncomputable def mapHomotopyEquiv {C D : ChainComplex B ℤ} (e : HomotopyEquiv C D) (n : ℤ) :
    HomotopyEquiv (dualCx D n) (dualCx C n) where
  hom := dualCx.map e.hom n
  inv := dualCx.map e.inv n
  homotopyHomInvId := (Homotopy.ofEq (dualCx.map_comp _ _ n).symm).trans
    ((mapHomotopy e.homotopyInvHomId n).trans (Homotopy.ofEq (dualCx.map_id _ n)))
  homotopyInvHomId := (Homotopy.ofEq (dualCx.map_comp _ _ n).symm).trans
    ((mapHomotopy e.homotopyHomInvId n).trans (Homotopy.ofEq (dualCx.map_id _ n)))

@[simp]
lemma mapHomotopyEquiv_hom {C D : ChainComplex B ℤ} (e : HomotopyEquiv C D) (n : ℤ) :
    (mapHomotopyEquiv e n).hom = dualCx.map e.hom n :=
  rfl

end dualCx

end HSP
