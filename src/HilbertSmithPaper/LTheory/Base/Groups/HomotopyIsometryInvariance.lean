import HilbertSmithPaper.LTheory.Base.Groups.LGroup
import HilbertSmithPaper.LTheory.Base.Pairs.CylinderCobordism

/-!
# Homotopy-isometry invariance

If `h : C ⟶ C'` is a chain homotopy equivalence between strict `k`-dimensional symmetric
Poincaré complexes `(C, φ)`, `(C', φ')` and `χ ∈ M(C')_{k+1}` satisfies `∂χ = h_% φ - φ'`, then
`[C, φ] = [C', φ']` in `L_k(B)`: the cylinder pair (with `P` all objects) is a cobordism.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- Homotopy-isometric strict symmetric Poincaré complexes have the same class in `L_k(B)`. -/
theorem LGroup.mk_eq_of_homotopyIsometry {k : ℤ} (x y : SymPoincare B k)
    (h : HomotopyEquiv x.C y.C) (χ : (StructureCx y.C).X (k + 1))
    (hχ : (StructureCx y.C).d (k + 1) k χ = (StructureCx.push h.hom).f k x.φ - y.φ) :
    LGroup.mk x = LGroup.mk y := by
  obtain ⟨W, hW, -⟩ := cylinder_cobordism ⊤ (fun _ _ _ _ _ _ => trivial) x y
    (fun _ => trivial) (fun _ => trivial) h χ hχ
  exact Quotient.sound (Cobordant.of_data_eq W hW)

end HSP
