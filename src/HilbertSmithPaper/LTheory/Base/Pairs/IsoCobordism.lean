import HilbertSmithPaper.LTheory.Base.Pairs.CylinderCobordism

/-!
# Isomorphic Poincaré complexes are cobordant

Let `(C, φ)` and `(C', φ')` be strict `k`-dimensional symmetric Poincaré complexes and
`u : C ⟶ C'` an isomorphism of complexes with `u_% φ = φ'`. Then `(C, φ)` is cobordant to
`(C', φ')`: the cylinder pair of `h = u` with `χ = 0` is a cobordism.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- Isomorphic strict symmetric Poincaré complexes with corresponding structures are cobordant. -/
lemma Cobordant.of_iso {k : ℤ} (x y : SymPoincare B k) (u : x.C ≅ y.C)
    (hu : (StructureCx.push u.hom).f k x.φ = y.φ) : Cobordant x y := by
  obtain ⟨W, hW, -⟩ := cylinder_cobordism ⊤ (fun _ _ _ _ _ _ => trivial) x y
    (fun _ => trivial) (fun _ => trivial) (HomotopyEquiv.ofIso u) 0
    (by rw [map_zero]; exact (sub_eq_zero.mpr hu).symm)
  exact Cobordant.of_data_eq W hW

end HSP
