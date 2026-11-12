import Mathlib

/-!
# The category of based ℚ-vector spaces

The category `ℚ` of based vector spaces: an object is `ℚ^d` (`d : ℕ`, wrapped in the structure
`FreeQ`), a morphism `ℚ^d → ℚ^{d'}` is a `d' × d` rational matrix (`toMatrix`, `ofMatrix`),
composition is the matrix product (`f ≫ g = g * f`) and the identity is the identity matrix. Sums
and scalar multiples are entrywise, making it a ℚ-linear category. The biproduct of `ℚ^d` and
`ℚ^{d'}` is `ℚ^{d+d'}` with the block inclusions and projections (indexed through
`finSumFinEquiv`), and `ℚ^0` is a zero object; these give finite biproducts.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

/-- **The category of based ℚ-vector spaces.** An object is the space `ℚ^d`, recorded by its
dimension `d`. -/
structure FreeQ : Type where
  /-- The dimension `d` of `ℚ^d`. -/
  dim : ℕ

namespace FreeQ

/-- Morphisms `ℚ^d → ℚ^{d'}` are `d' × d` rational matrices; composition is the matrix product. -/
instance instCategory : Category FreeQ where
  Hom X Y := Matrix (Fin Y.dim) (Fin X.dim) ℚ
  id X := (1 : Matrix (Fin X.dim) (Fin X.dim) ℚ)
  comp {X Y Z} f g := (show Matrix (Fin Z.dim) (Fin Y.dim) ℚ from g) *
    (show Matrix (Fin Y.dim) (Fin X.dim) ℚ from f)
  id_comp _ := Matrix.mul_one _
  comp_id _ := Matrix.one_mul _
  assoc _ _ _ := (Matrix.mul_assoc _ _ _).symm

/-- A morphism as a matrix. -/
abbrev toMatrix {X Y : FreeQ} (f : X ⟶ Y) : Matrix (Fin Y.dim) (Fin X.dim) ℚ := f

/-- A matrix as a morphism. -/
abbrev ofMatrix {X Y : FreeQ} (A : Matrix (Fin Y.dim) (Fin X.dim) ℚ) : X ⟶ Y := A

@[simp]
lemma comp_toMatrix {X Y Z : FreeQ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toMatrix (f ≫ g) = toMatrix g * toMatrix f := rfl

@[simp]
lemma id_toMatrix (X : FreeQ) : toMatrix (𝟙 X) = 1 := rfl

instance instAddCommGroupHom (X Y : FreeQ) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (Matrix (Fin Y.dim) (Fin X.dim) ℚ))

instance instModuleHom (X Y : FreeQ) : Module ℚ (X ⟶ Y) :=
  inferInstanceAs (Module ℚ (Matrix (Fin Y.dim) (Fin X.dim) ℚ))

instance instPreadditive : Preadditive FreeQ where
  add_comp _ _ _ f f' g := Matrix.mul_add (toMatrix g) (toMatrix f) (toMatrix f')
  comp_add _ _ _ f g g' := Matrix.add_mul (toMatrix g) (toMatrix g') (toMatrix f)

instance instLinear : Linear ℚ FreeQ where
  smul_comp _ _ _ r f g := Matrix.mul_smul (toMatrix g) r (toMatrix f)
  comp_smul _ _ _ f r g := Matrix.smul_mul r (toMatrix g) (toMatrix f)

@[simp]
lemma add_toMatrix {X Y : FreeQ} (f g : X ⟶ Y) : toMatrix (f + g) = toMatrix f + toMatrix g :=
  rfl

@[simp]
lemma smul_toMatrix {X Y : FreeQ} (c : ℚ) (f : X ⟶ Y) : toMatrix (c • f) = c • toMatrix f := rfl

@[simp]
lemma zero_toMatrix {X Y : FreeQ} : toMatrix (0 : X ⟶ Y) = 0 := rfl

/-- The block biproduct bicone of `ℚ^a` and `ℚ^b`, with point `ℚ^{a+b}`. -/
private def biprodBicone (X Y : FreeQ) : BinaryBicone X Y where
  pt := ⟨X.dim + Y.dim⟩
  fst := ofMatrix ((Matrix.fromCols 1 0).submatrix id finSumFinEquiv.symm)
  snd := ofMatrix ((Matrix.fromCols 0 1).submatrix id finSumFinEquiv.symm)
  inl := ofMatrix ((Matrix.fromRows 1 0).submatrix finSumFinEquiv.symm id)
  inr := ofMatrix ((Matrix.fromRows 0 1).submatrix finSumFinEquiv.symm id)
  inl_fst := by
    change (Matrix.fromCols 1 0).submatrix id finSumFinEquiv.symm *
      (Matrix.fromRows 1 0).submatrix finSumFinEquiv.symm id = (1 : Matrix (Fin X.dim) (Fin X.dim) ℚ)
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.submatrix_id_id]
    simp
  inl_snd := by
    change (Matrix.fromCols 0 1).submatrix id finSumFinEquiv.symm *
      (Matrix.fromRows 1 0).submatrix finSumFinEquiv.symm id = 0
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.submatrix_id_id]
    simp
  inr_fst := by
    change (Matrix.fromCols 1 0).submatrix id finSumFinEquiv.symm *
      (Matrix.fromRows 0 1).submatrix finSumFinEquiv.symm id = 0
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.submatrix_id_id]
    simp
  inr_snd := by
    change (Matrix.fromCols 0 1).submatrix id finSumFinEquiv.symm *
      (Matrix.fromRows 0 1).submatrix finSumFinEquiv.symm id = (1 : Matrix (Fin Y.dim) (Fin Y.dim) ℚ)
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.submatrix_id_id]
    simp

private lemma block_total (a b : ℕ) :
    (Matrix.fromRows (1 : Matrix (Fin a) (Fin a) ℚ) (0 : Matrix (Fin b) (Fin a) ℚ)).submatrix
        finSumFinEquiv.symm id *
      (Matrix.fromCols (1 : Matrix (Fin a) (Fin a) ℚ) (0 : Matrix (Fin a) (Fin b) ℚ)).submatrix
        id finSumFinEquiv.symm +
    (Matrix.fromRows (0 : Matrix (Fin a) (Fin b) ℚ) (1 : Matrix (Fin b) (Fin b) ℚ)).submatrix
        finSumFinEquiv.symm id *
      (Matrix.fromCols (0 : Matrix (Fin b) (Fin a) ℚ) (1 : Matrix (Fin b) (Fin b) ℚ)).submatrix
        id finSumFinEquiv.symm =
      (1 : Matrix (Fin (a + b)) (Fin (a + b)) ℚ) := by
  rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.fromRows_mul_fromCols,
    Matrix.fromRows_mul_fromCols]
  have hadd : ∀ A B : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℚ,
      A.submatrix finSumFinEquiv.symm finSumFinEquiv.symm +
        B.submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      (A + B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := fun _ _ => rfl
  rw [hadd]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.fromBlocks_add,
    add_zero, zero_add, Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv finSumFinEquiv.symm

private lemma biprodBicone_total (X Y : FreeQ) :
    (biprodBicone X Y).fst ≫ (biprodBicone X Y).inl +
      (biprodBicone X Y).snd ≫ (biprodBicone X Y).inr = 𝟙 _ :=
  block_total X.dim Y.dim

instance instHasBinaryBiproducts : HasBinaryBiproducts FreeQ :=
  ⟨fun X Y => hasBinaryBiproduct_of_total (biprodBicone X Y) (biprodBicone_total X Y)⟩

/-- `ℚ^0` is a zero object. -/
lemma isZero_zero : IsZero (⟨0⟩ : FreeQ) :=
  (IsZero.iff_id_eq_zero _).2 (Matrix.ext fun i => i.elim0)

instance instHasZeroObject : HasZeroObject FreeQ := ⟨⟨⟨0⟩, isZero_zero⟩⟩

instance instHasFiniteBiproducts : HasFiniteBiproducts FreeQ :=
  have : HasFiniteProducts FreeQ := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end FreeQ

end HSP
