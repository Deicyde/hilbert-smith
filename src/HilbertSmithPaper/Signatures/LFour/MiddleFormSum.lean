import Mathlib
import HilbertSmithPaper.Signatures.LFour.MiddleForm
import HilbertSmithPaper.LTheory.Base.Pairs.SumOfPoincare

/-!
# Middle form of a sum

For strict `4`-dimensional complexes `(C, φ)` and `(C', φ')` and a complex `(C'', φ'')` equal to
their sum `(C ⊕ C', φ ⊕ φ')`, the map `H^2(C ⊕ C'; ℝ) → H^2(C; ℝ) × H^2(C'; ℝ)` induced on real
cochains by the transposes of the two inclusions is a bijective, `G`-equivariant isometry from
`b_{C ⊕ C'}` to `b_C ⊥ b_{C'}` (`HSP.middleForm_sum`).

Lean encoding: the sum `HSP.SymPoincare.sum` is chosen, equal to `(C ⊕ C', φ ⊕ φ')` as a
structured complex (an equality in `Σ C, M(C)_4`), so the statement is for any `(C'', φ'')` with
this equality `h`, and the inclusions are transported along the equality of complexes it gives.
-/

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The middle form of a sum is the orthogonal sum of the middle forms. -/
theorem middleForm_sum (x y z : SymPoincare (Karoubi (FreeCat G)) 4)
    (h : (⟨z.C, z.φ⟩ : Σ C : ChainComplex (Karoubi (FreeCat G)) ℤ, (StructureCx C).X 4) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩) :
    let Ψ : realHco z.C 2 →ₗ[ℝ] realHco x.C 2 × realHco y.C 2 :=
      (realHco.map (biprod.inl ≫ eqToHom (congrArg Sigma.fst h).symm)).prod
        (realHco.map (biprod.inr ≫ eqToHom (congrArg Sigma.fst h).symm))
    Function.Bijective Ψ ∧
      (∀ u v, middleForm z u v = middleForm x (Ψ u).1 (Ψ v).1 + middleForm y (Ψ u).2 (Ψ v).2) ∧
      ∀ (g : Multiplicative G) (u : realHco z.C 2),
        Ψ (realHco.rep g u) = (realHco.rep g (Ψ u).1, realHco.rep g (Ψ u).2) := by
  sorry

end HSP
