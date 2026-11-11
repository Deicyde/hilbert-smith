import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair

/-!
# Transport of pairs along isomorphisms

If `(f : C ⟶ D, δφ, φ)` is a strict `n`-dimensional Poincaré pair, `u : C' ≅ C` an isomorphism
of complexes, `φ' ∈ M(C')_m` with `u_% φ' = φ`, and `s ∈ {1, -1}` (a unit of `ℤ`), then
`(f ∘ u, s δφ, s φ')` is a strict `n`-dimensional Poincaré pair.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- Transport of a pair along an isomorphism `u : C' ≅ C` of its boundary complex carrying
`φ'` to `φ`, combined with the sign `s ∈ {1, -1}`. -/
theorem SymPair.transport {m n : ℤ} (W : SymPair B m n) {C' : ChainComplex B ℤ} (u : C' ≅ W.C)
    (φ' : (StructureCx C').X m) (hφ' : (StructureCx.push u.hom).f m φ' = W.φ) (s : ℤˣ) :
    ∃ W' : SymPair B m n, W'.data = ⟨C', W.D, u.hom ≫ W.f, s • W.δφ, s • φ'⟩ := by
  sorry

end HSP
