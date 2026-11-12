import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Complexes.SumOfComplexes

/-!
# Cobordism

Strict `k`-dimensional symmetric Poincaré complexes `(C, φ)` and `(C', φ')` are *cobordant* if
there is a strict `(k+1)`-dimensional Poincaré pair with boundary `(C ⊕ C', φ ⊕ (-φ'))`.

Lean: the boundary of the pair `W` equals `(C ⊞ C', φ ⊕ (-φ'))` as an element of the type of
structured complexes `Σ C, M(C)_k`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- `(C, φ)` and `(C', φ')` are *cobordant* if some strict `(k+1)`-dimensional Poincaré pair has
boundary `(C ⊞ C', φ ⊕ (-φ'))`. -/
def Cobordant {k : ℤ} (x y : SymPoincare B k) : Prop :=
  ∃ W : SymPair B k (k + 1),
    (⟨W.C, W.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X k) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ (-y.φ)⟩

private lemma sigma_of_data {m n : ℤ} (W : SymPair B m n) {C D : ChainComplex B ℤ}
    {f : C ⟶ D} {δφ : (StructureCx D).X n} {φ : (StructureCx C).X m}
    (h : W.data = ⟨C, D, f, δφ, φ⟩) :
    (⟨W.C, W.φ⟩ : Σ C : ChainComplex B ℤ, (StructureCx C).X m) = ⟨C, φ⟩ := by
  obtain ⟨C₀, D₀, f₀, δφ₀, φ₀⟩ := W
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h)
  have h' := eq_of_heq h
  simp only [Prod.mk.injEq] at h'
  exact congrArg (Sigma.mk C₀) h'.2.2

/-- A pair whose data has boundary `(C ⊞ C', φ ⊕ (-φ'))` is a cobordism. -/
lemma Cobordant.of_data_eq {k : ℤ} {x y : SymPoincare B k} (W : SymPair B k (k + 1))
    {D : ChainComplex B ℤ} {f : x.C ⊞ y.C ⟶ D} {δφ : (StructureCx D).X (k + 1)}
    (h : W.data = ⟨x.C ⊞ y.C, D, f, δφ, StructureCx.sum x.φ (-y.φ)⟩) : Cobordant x y :=
  ⟨W, sigma_of_data W h⟩

end HSP
