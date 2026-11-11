import HilbertSmithPaper.LTheory.Base.Complexes.StructurePush
import HilbertSmithPaper.LTheory.Base.Categories.DualBinaryBiproducts

/-!
# Sum of structured complexes

`(C, φ) ⊕ (C', φ') = (C ⊞ C', φ ⊕ φ')` with `φ ⊕ φ' = i_% φ + i'_% φ'`, where
`i : C ⟶ C ⊞ C'` and `i' : C' ⟶ C ⊞ C'` are the inclusions. In degree `r` this is
`φ_r ⊕ φ'_r` precomposed with the canonical isomorphism
`(C_{n-r} ⊞ C'_{n-r})^* ≅ C_{n-r}^* ⊞ C'^*_{n-r}`, whose components are the duals of the
inclusions; this holds because the duality is additive.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The sum `φ ⊕ φ' ∈ M(C ⊞ C')_n` of structures `φ ∈ M(C)_n`, `φ' ∈ M(C')_n`:
`φ ⊕ φ' = i_% φ + i'_% φ'` for the inclusions `i`, `i'` of the summands. -/
noncomputable def StructureCx.sum {C C' : ChainComplex B ℤ} {n : ℤ} (φ : (StructureCx C).X n)
    (φ' : (StructureCx C').X n) : (StructureCx (C ⊞ C')).X n :=
  (StructureCx.push biprod.inl).f n φ + (StructureCx.push biprod.inr).f n φ'

end HSP
