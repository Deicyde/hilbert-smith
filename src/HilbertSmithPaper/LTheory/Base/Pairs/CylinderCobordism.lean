import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism

/-!
# Homotopy-isometric complexes are cobordant

Let `P` be a class of objects closed under sums of two objects (the cone point of any biproduct
bicone of two objects of `P` is in `P`), `(C, φ)`,
`(C', φ')` strict `k`-dimensional symmetric Poincaré complexes with chain objects in `P`,
`h : C ⟶ C'` a chain homotopy equivalence and `χ ∈ M(C')_{k+1}` with `∂χ = h_% φ - φ'`. With
`χ' = (χ + Tχ)/2`, `((h, 1) : C ⊞ C' ⟶ C', χ', φ ⊕ (-φ'))` is a strict `(k+1)`-dimensional
Poincaré pair whose chain objects lie in `P`; its boundary is `(C ⊞ C', φ ⊕ (-φ'))`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The cylinder pair `((h, 1) : C ⊞ C' ⟶ C', (χ + Tχ)/2, φ ⊕ (-φ'))` of a homotopy isometry
is a strict `(k+1)`-dimensional Poincaré pair with chain objects in `P`. -/
theorem cylinder_cobordism (P : ObjectProperty B)
    (hsum : ∀ (X Y : B) (c : BinaryBicone X Y), c.IsBilimit → P X → P Y → P c.pt)
    {k : ℤ} (x y : SymPoincare B k)
    (hx : ∀ r, P (x.C.X r)) (hy : ∀ r, P (y.C.X r)) (h : HomotopyEquiv x.C y.C)
    (χ : (StructureCx y.C).X (k + 1))
    (hχ : (StructureCx y.C).d (k + 1) k χ = (StructureCx.push h.hom).f k x.φ - y.φ) :
    ∃ W : SymPair B k (k + 1),
      W.data = ⟨x.C ⊞ y.C, y.C, biprod.desc h.hom (𝟙 y.C),
        (1 / 2 : ℚ) • (χ + (StructureCx.T y.C).f (k + 1) χ), StructureCx.sum x.φ (-y.φ)⟩ ∧
      ∀ r, P (W.C.X r) ∧ P (W.D.X r) := by
  sorry

end HSP
