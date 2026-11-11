import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism

/-!
# Bounded extension of a unitary isomorphism

Let `η : F ≅ G` be a unitary natural isomorphism of duality functors `A → B`. Put
`C_{ℤ^0} η = η`, and let `C_{ℤ^{j+1}} η` have at `M = (M_n)_n` the diagonal matrix with entries
`(C_{ℤ^j} η)_{M_n}`, of propagation `0`. Then `C_{ℤ^j} η : C_{ℤ^j} F ≅ C_{ℤ^j} G` is a unitary
natural isomorphism of the bounded extensions: naturality and unitarity hold entrywise.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

namespace Bounded

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

omit [HasFiniteBiproducts A'] [DualCat A'] in
/-- The diagonal isomorphism with entries `e n : M_n ≅ N_n`. -/
private def diagIsoU {M N : Bounded A'} (e : ∀ n, M.X n ≅ N.X n) : M ≅ N where
  hom := diag fun n => (e n).hom
  inv := diag fun n => (e n).inv
  hom_inv_id := by rw [diag_comp_diag]; simp only [Iso.hom_inv_id]; rfl
  inv_hom_id := by rw [diag_comp_diag]; simp only [Iso.inv_hom_id]; rfl

private lemma dualHom_diag {M N : Bounded A'} (d : ∀ n, M.X n ⟶ N.X n) :
    dualHom (diag d) = diag (M := dual N) (N := dual M) (fun n => dualHom (d n)) :=
  hom_ext fun a b => by
    rw [dualHom_apply]
    change dualHom (diagF d b a) = diagF (M := dual N) (N := dual M) (fun n => dualHom (d n)) a b
    by_cases h : a = b
    · subst h
      rw [diagF_self, diagF_self]
    · rw [diagF_ne _ (Ne.symm h), diagF_ne _ h, dualHom_zero]

/-- One level: the diagonal extension `C_ℤ η : C_ℤ F ≅ C_ℤ G` of a unitary isomorphism. -/
private def mapUnitaryIso {F G : DualFunctor A A'} (η : DualFunctor.UnitaryIso F G) :
    DualFunctor.UnitaryIso (map F) (map G) where
  iso := NatIso.ofComponents (fun M => diagIsoU (M := (map F).toFunctor.obj M)
      (N := (map G).toFunctor.obj M) fun n => η.iso.app (M.X n)) (by
    intro M N f
    refine hom_ext fun a b => ?_
    exact (compF_diagF (M := ⟨fun n => F.toFunctor.obj (M.X n)⟩)
        (N := ⟨fun n => F.toFunctor.obj (N.X n)⟩) (P := ⟨fun n => G.toFunctor.obj (N.X n)⟩)
        (fun m n => F.toFunctor.map (f.1 m n)) (fun n => (η.iso.app (N.X n)).hom) a b).trans
      ((η.iso.hom.naturality (f.1 a b)).trans
        (diagF_compF (M := ⟨fun n => F.toFunctor.obj (M.X n)⟩)
          (N := ⟨fun n => G.toFunctor.obj (M.X n)⟩) (P := ⟨fun n => G.toFunctor.obj (N.X n)⟩)
          (fun n => (η.iso.app (M.X n)).hom) (fun m n => G.toFunctor.map (f.1 m n)) a b).symm))
  unitary M := by
    simp only [NatIso.ofComponents_hom_app, diagIsoU, map_ξ_hom, dualHom_diag]
    erw [diag_comp_diag, diag_comp_diag]
    congr 1
    funext n
    exact η.unitary (M.X n)

/-- The bounded extensions `C_{ℤ^j} η : C_{ℤ^j} F ≅ C_{ℤ^j} G` of a unitary isomorphism `η`:
`η` for `j = 0` and the diagonal extension of the previous level otherwise. -/
def unitaryIsoIter {F G : DualFunctor A A'} (η : DualFunctor.UnitaryIso F G) :
    ∀ j : ℕ, DualFunctor.UnitaryIso (mapIter F j) (mapIter G j)
  | 0 => η
  | j + 1 => mapUnitaryIso (unitaryIsoIter η j)

end Bounded

end HSP
