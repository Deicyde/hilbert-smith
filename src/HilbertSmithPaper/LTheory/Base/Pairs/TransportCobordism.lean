import HilbertSmithPaper.LTheory.Base.Pairs.Cobordism
import HilbertSmithPaper.LTheory.Base.Pairs.PairTransport

/-!
# Transported pairs are cobordisms

Let `(C, φ)`, `(C', φ')` be strict `k`-dimensional symmetric Poincaré complexes,
`(f : E ⟶ D, δψ, ψ)` a strict `(k+1)`-dimensional Poincaré pair, `u : C ⊞ C' ⟶ E` an isomorphism,
`φ'' ∈ M(C ⊞ C')_k` with `u_% φ'' = ψ`, and `s = ±1` with `s φ'' = φ ⊕ (-φ')`. Then `(C, φ)` is
cobordant to `(C', φ')`: transport the pair along `u` with the sign `s`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- A pair transported along an isomorphism onto `C ⊞ C'`, with boundary structure
`φ ⊕ (-φ')`, makes `(C, φ)` cobordant to `(C', φ')`. -/
lemma Cobordant.of_transport {k : ℤ} (x y : SymPoincare B k) (W : SymPair B k (k + 1))
    (u : x.C ⊞ y.C ≅ W.C) (φ' : (StructureCx (x.C ⊞ y.C)).X k)
    (hu : (StructureCx.push u.hom).f k φ' = W.φ) (s : ℤˣ)
    (hs : s • φ' = StructureCx.sum x.φ (-y.φ)) : Cobordant x y := by
  obtain ⟨W', hW'⟩ := W.transport u φ' hu s
  exact Cobordant.of_data_eq (D := W.D) (f := u.hom ≫ W.f) (δφ := s • W.δφ) W'
    (by rw [hW', hs])

end HSP
