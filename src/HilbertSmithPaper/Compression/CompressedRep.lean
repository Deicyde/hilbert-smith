import Mathlib
import HilbertSmithPaper.Compression.CompressedComplex

/-!
# Morphisms represented by compressed matrices

A morphism `f : C_r → C_s` of `𝒜_𝟏(T × Sⁿ)` between degrees of the compressed complex is
*represented* by a sequence of rational matrices `m_i` on the retained cells if it is the class of
the sequence `(m_i)`, each `m_i` read as a matrix over the trivial group.

## Encoding

`IsCompressedRep F f m` (the declaration of the article) asks for a morphism `u` of sequences
(`AsymPre`) whose level-`i` matrix, on the basis `Unit × Fin _` of the trivial group, is
`(a, b) ↦ m_i a.2 b.2`, with `f = [u]`. Its propagation tends to `0` because `u` is a morphism.
-/

namespace HSP.Compression

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The morphism `f : C_r → C_s` of `𝒜_𝟏(T × Sⁿ)` is the class of the sequence of rational
matrices `m_i` on the retained cells. -/
def IsCompressedRep (F : FixedLocalData p n D ρplus) {r s : ℤ}
    (f : compressed F r ⟶ compressed F s)
    (m : ∀ i, Matrix (Fin ((compressed F s).as.n i)) (Fin ((compressed F r).as.n i)) ℚ) :
    Prop :=
  ∃ u : (compressed F r).as ⟶ (compressed F s).as,
    (∀ i, FreeCat.mat (AsymPre.coord u i) = fun a b => m i a.2 b.2) ∧ f = AsymCat.mkHom u

end HSP.Compression
