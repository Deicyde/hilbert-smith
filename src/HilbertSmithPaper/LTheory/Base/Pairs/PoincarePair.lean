import HilbertSmithPaper.LTheory.Base.Pairs.SymmetricPoincareComplex
import HilbertSmithPaper.LTheory.Base.Pairs.PairMap

/-!
# Strict Poincaré pair

A strict `n`-dimensional symmetric Poincaré pair `(f : C ⟶ D, δφ, φ)` in a duality category `B`:
with `m = n - 1`, `(C, φ)` is a strict `m`-dimensional symmetric Poincaré complex, `D_r` is a
zero object for `r` outside `[0, n]`, `δφ ∈ M(D)_n`, `T δφ = δφ`, `∂δφ = f_% φ`, and the pair map
`ψ : D^{n-*} ⟶ 𝒞(f)` is a chain homotopy equivalence. Its boundary is `(C, φ)`.

Lean: `SymPair B m n` carries both dimensions, with the field `dim : m + 1 = n`, so that a pair
whose boundary is `m`-dimensional needs no transport along `n - 1 = m`. The boundary conditions
are fields; `SymPair.boundary` packages `(C, φ)` as a `SymPoincare B m`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

/-- A *strict `n`-dimensional symmetric Poincaré pair* `(f : C ⟶ D, δφ, φ)` with boundary
`(C, φ)` of dimension `m = n - 1`. -/
structure SymPair (B : Type u) [Category.{v} B] [Preadditive B] [Linear ℚ B]
    [HasFiniteBiproducts B] [DualCat B] (m n : ℤ) where
  /-- The boundary complex `C`. -/
  C : ChainComplex B ℤ
  /-- The complex `D`. -/
  D : ChainComplex B ℤ
  /-- The chain map `f : C ⟶ D`. -/
  f : C ⟶ D
  /-- The structure `δφ ∈ M(D)_n`. -/
  δφ : (StructureCx D).X n
  /-- The boundary structure `φ ∈ M(C)_m`. -/
  φ : (StructureCx C).X m
  /-- `m = n - 1`. -/
  dim : m + 1 = n
  /-- `C_r` is a zero object for `r` outside `[0, m]`. -/
  boundary_bounded : ∀ r : ℤ, r < 0 ∨ m < r → IsZero (C.X r)
  /-- `∂φ = 0`. -/
  boundary_cycle : (StructureCx C).d m (m - 1) φ = 0
  /-- `T φ = φ`. -/
  boundary_symmetric : (StructureCx.T C).f m φ = φ
  /-- `φ_♮ : C^{m-*} ⟶ C` is a chain homotopy equivalence. -/
  boundary_poincare : ∃ e : HomotopyEquiv (dualCx C m) C,
    e.hom = StructureCx.toHom φ boundary_cycle
  /-- `D_r` is a zero object for `r` outside `[0, n]`. -/
  bounded : ∀ r : ℤ, r < 0 ∨ n < r → IsZero (D.X r)
  /-- `T δφ = δφ`. -/
  symmetric : (StructureCx.T D).f n δφ = δφ
  /-- `∂δφ = f_% φ`. -/
  rel : (StructureCx D).d n m δφ = (StructureCx.push f).f m φ
  /-- The pair map `ψ : D^{n-*} ⟶ 𝒞(f)` is a chain homotopy equivalence. -/
  poincare : ∃ e : HomotopyEquiv (dualCx D n) (cone f),
    e.hom = pairMap f dim δφ φ boundary_cycle rel

namespace SymPair

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The boundary `(C, φ)` of a pair, a strict `m`-dimensional symmetric Poincaré complex. -/
@[simps]
def boundary {m n : ℤ} (W : SymPair B m n) : SymPoincare B m where
  C := W.C
  φ := W.φ
  bounded := W.boundary_bounded
  cycle := W.boundary_cycle
  symmetric := W.boundary_symmetric
  poincare := W.boundary_poincare

end SymPair

/-! Non-vacuity: the zero pair over a toy duality category with one object and zero morphisms. -/

private def Toy : Type := PUnit

private instance : Category Toy where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

private instance (X Y : Toy) : Subsingleton (X ⟶ Y) := inferInstanceAs (Subsingleton PUnit)

private instance : Preadditive Toy where
  homGroup _ _ := inferInstanceAs (AddCommGroup PUnit)
  add_comp _ _ _ _ _ _ := Subsingleton.elim _ _
  comp_add _ _ _ _ _ _ := Subsingleton.elim _ _

private instance : Linear ℚ Toy where
  homModule _ _ := inferInstanceAs (Module ℚ PUnit)
  smul_comp _ _ _ _ _ _ := Subsingleton.elim _ _
  comp_smul _ _ _ _ _ _ := Subsingleton.elim _ _

private lemma toy_isZero (X : Toy) : IsZero X :=
  ⟨fun _ => ⟨⟨⟨PUnit.unit⟩, fun _ => Subsingleton.elim _ _⟩⟩,
    fun _ => ⟨⟨⟨PUnit.unit⟩, fun _ => Subsingleton.elim _ _⟩⟩⟩

private instance : HasFiniteBiproducts Toy where
  out _ := ⟨fun _ => HasBiproduct.mk
    { bicone :=
        { pt := (PUnit.unit : Toy)
          π := fun _ => PUnit.unit
          ι := fun _ => PUnit.unit
          ι_π := fun _ _ => Subsingleton.elim _ _ }
      isBilimit :=
        { isLimit :=
            { lift := fun _ => PUnit.unit
              fac := fun _ _ => Subsingleton.elim _ _
              uniq := fun _ _ _ => Subsingleton.elim _ _ }
          isColimit :=
            { desc := fun _ => PUnit.unit
              fac := fun _ _ => Subsingleton.elim _ _
              uniq := fun _ _ _ => Subsingleton.elim _ _ } } }⟩

private instance : DualCat Toy where
  dual X := X
  dualHom _ := PUnit.unit
  dualHom_id _ := Subsingleton.elim _ _
  dualHom_comp _ _ := Subsingleton.elim _ _
  dualHom_add _ _ := Subsingleton.elim _ _
  dualHom_smul _ _ := Subsingleton.elim _ _
  dual_dual _ := rfl
  dualHom_dualHom _ := Subsingleton.elim _ _
  dualHom_zero := Subsingleton.elim _ _
  dualHom_neg _ := Subsingleton.elim _ _
  dualHom_sub _ _ := Subsingleton.elim _ _
  dualHom_eqToHom _ := Subsingleton.elim _ _

/-- The complex of `Toy` with every object the unique object. -/
private def toyCx : ChainComplex Toy ℤ where
  X _ := (PUnit.unit : Toy)
  d _ _ := (PUnit.unit : PUnit)
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := rfl

private instance (K L : ChainComplex Toy ℤ) : Subsingleton (K ⟶ L) :=
  ⟨fun _ _ => HomologicalComplex.Hom.ext (funext fun _ => Subsingleton.elim _ _)⟩

private instance (K : ChainComplex Toy ℤ) (n : ℤ) : Subsingleton ((StructureCx K).X n) :=
  ⟨fun _ _ => funext fun _ => Subsingleton.elim _ _⟩

private def toyIso (K L : ChainComplex Toy ℤ) : K ≅ L where
  hom := ⟨fun _ => PUnit.unit, fun _ _ _ => Subsingleton.elim _ _⟩
  inv := ⟨fun _ => PUnit.unit, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The zero pair `(0 : C ⟶ D, 0, 0)` over `Toy`, in every dimension. -/
private def toyPair (m : ℤ) : SymPair Toy m (m + 1) where
  C := toyCx
  D := toyCx
  f := 𝟙 _
  δφ := 0
  φ := 0
  dim := rfl
  boundary_bounded _ _ := toy_isZero _
  boundary_cycle := Subsingleton.elim _ _
  boundary_symmetric := Subsingleton.elim _ _
  boundary_poincare := ⟨HomotopyEquiv.ofIso (toyIso _ _), Subsingleton.elim _ _⟩
  bounded _ _ := toy_isZero _
  symmetric := Subsingleton.elim _ _
  rel := Subsingleton.elim _ _
  poincare := ⟨HomotopyEquiv.ofIso (toyIso _ _), Subsingleton.elim _ _⟩

private lemma symPair_nonempty (m : ℤ) : Nonempty (SymPair Toy m (m + 1)) := ⟨toyPair m⟩

end HSP
