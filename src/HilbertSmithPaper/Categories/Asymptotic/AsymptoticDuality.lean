import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory
import HilbertSmithPaper.Categories.Asymptotic.PropTranspose
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Duality on the asymptotic category

`𝒜_𝐆(X)` is a strict duality category under `M^* = M` and `[u_i]^* = [u_iᵀ]`.

Lean encoding. On sequences, `HSP.AsymPre.transpose u` is the levelwise transpose (the duality
of `Free(ℚ[G_i])`), which keeps propagation (`HSP.prop_transpose`); it respects eventual
equality, so it descends to the quotient (`HSP.AsymCat.dualCat`). Transposition reverses
composition, is `ℚ`-linear and is an involution on the nose.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

/-- The levelwise transpose `(u_iᵀ)` of a sequence of matrices. -/
def transpose {M N : AsymPre G X} (u : M ⟶ N) : N ⟶ M :=
  homMk (fun i => DualCat.dualHom (coord u i)) (by
    refine (tendsto_congr fun i => ?_).2 (tendsto_prop u)
    exact prop_transpose (M.label i) (N.label i) (FreeCat.mat (coord u i)))

@[simp] theorem coord_transpose {M N : AsymPre G X} (u : M ⟶ N) (i : ℕ) :
    coord (transpose u) i = DualCat.dualHom (coord u i) := rfl

theorem transpose_id (M : AsymPre G X) : transpose (𝟙 M) = 𝟙 M :=
  hom_ext fun i => DualCat.dualHom_id (M.free i)

theorem transpose_comp {M N P : AsymPre G X} (u : M ⟶ N) (v : N ⟶ P) :
    transpose (u ≫ v) = transpose v ≫ transpose u :=
  hom_ext fun i => DualCat.dualHom_comp (coord u i) (coord v i)

theorem transpose_add {M N : AsymPre G X} (u v : M ⟶ N) :
    transpose (u + v) = transpose u + transpose v :=
  hom_ext fun i => DualCat.dualHom_add (coord u i) (coord v i)

theorem transpose_smul {M N : AsymPre G X} (c : ℚ) (u : M ⟶ N) :
    transpose (c • u) = c • transpose u :=
  hom_ext fun i => DualCat.dualHom_smul c (coord u i)

theorem transpose_transpose {M N : AsymPre G X} (u : M ⟶ N) : transpose (transpose u) = u :=
  hom_ext fun i => FreeCat.hom_ext (Matrix.transpose_transpose (FreeCat.mat (coord u i)))

end AsymPre

namespace AsymCat

/-- The dual `[u]^* = [uᵀ]` of a morphism. -/
def dualHom' {P Q : AsymCat G X} (f : P ⟶ Q) : Q ⟶ P :=
  Quot.lift (fun u : P.as ⟶ Q.as => mkHom (AsymPre.transpose u)) (fun a b h => by
    rw [HomRel.compClosure_iff_self] at h
    exact (mkHom_eq_iff _ _).2 (h.mono fun i hi => by simp [hi])) f

theorem dualHom'_mkHom {M N : AsymPre G X} (u : M ⟶ N) :
    dualHom' (mkHom u) = mkHom (AsymPre.transpose u) := rfl

private theorem mkHom_add {M N : AsymPre G X} (u v : M ⟶ N) :
    mkHom (u + v) = mkHom u + mkHom v :=
  (Quotient.functor (asymRel G X)).map_add

private theorem mkHom_smul {M N : AsymPre G X} (c : ℚ) (u : M ⟶ N) :
    mkHom (c • u) = c • mkHom u :=
  (Quotient.functor (asymRel G X)).map_smul c u

private theorem dualHom'_id (P : AsymCat G X) : dualHom' (𝟙 P) = 𝟙 P := by
  show dualHom' (mkHom (𝟙 P.as)) = mkHom (𝟙 P.as)
  rw [dualHom'_mkHom, AsymPre.transpose_id]

/-- `𝒜_𝐆(X)` is a strict duality category under `M^* = M` and `[u_i]^* = [u_iᵀ]`. -/
instance dualCat : DualCat (AsymCat G X) where
  dual P := P
  dualHom f := dualHom' f
  dualHom_id P := dualHom'_id P
  dualHom_comp f g := by
    obtain ⟨u, rfl⟩ := mkHom_surjective f
    obtain ⟨v, rfl⟩ := mkHom_surjective g
    rw [← Functor.map_comp, dualHom'_mkHom, dualHom'_mkHom, dualHom'_mkHom,
      AsymPre.transpose_comp]
    exact (Quotient.functor (asymRel G X)).map_comp _ _
  dualHom_add f g := by
    obtain ⟨u, rfl⟩ := mkHom_surjective f
    obtain ⟨v, rfl⟩ := mkHom_surjective g
    rw [← mkHom_add, dualHom'_mkHom, dualHom'_mkHom, dualHom'_mkHom, AsymPre.transpose_add,
      mkHom_add]
  dualHom_smul c f := by
    obtain ⟨u, rfl⟩ := mkHom_surjective f
    rw [← mkHom_smul, dualHom'_mkHom, dualHom'_mkHom, AsymPre.transpose_smul, mkHom_smul]
  dual_dual _ := rfl
  dualHom_dualHom f := by
    obtain ⟨u, rfl⟩ := mkHom_surjective f
    rw [dualHom'_mkHom, dualHom'_mkHom, AsymPre.transpose_transpose, eqToHom_refl,
      eqToHom_refl, Category.id_comp, Category.comp_id]
  dualHom_zero := by
    intro P Q
    rw [← (Quotient.functor (asymRel G X)).map_zero, dualHom'_mkHom]
    exact congrArg mkHom (AsymPre.hom_ext fun _ => DualCat.dualHom_zero)
  dualHom_neg f := by
    obtain ⟨u, rfl⟩ := mkHom_surjective f
    rw [← (Quotient.functor (asymRel G X)).map_neg, dualHom'_mkHom, dualHom'_mkHom,
      ← (Quotient.functor (asymRel G X)).map_neg]
    exact congrArg mkHom (AsymPre.hom_ext fun i => DualCat.dualHom_neg _)
  dualHom_sub f g := by
    obtain ⟨u, rfl⟩ := mkHom_surjective f
    obtain ⟨v, rfl⟩ := mkHom_surjective g
    rw [← (Quotient.functor (asymRel G X)).map_sub, dualHom'_mkHom, dualHom'_mkHom,
      dualHom'_mkHom, ← (Quotient.functor (asymRel G X)).map_sub]
    exact congrArg mkHom (AsymPre.hom_ext fun i => DualCat.dualHom_sub _ _)
  dualHom_eqToHom h := by
    subst h
    exact dualHom'_id _

@[simp] theorem dualHom_mkHom {M N : AsymPre G X} (u : M ⟶ N) :
    DualCat.dualHom (mkHom u) = mkHom (AsymPre.transpose u) := rfl

end AsymCat

end HSP
