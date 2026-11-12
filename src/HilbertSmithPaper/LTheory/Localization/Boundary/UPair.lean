import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFunctor
import HilbertSmithPaper.LTheory.Base.Pairs.FunctorPoincare
import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Categories.SubcategoryInclusion
import HilbertSmithPaper.LTheory.Base.Categories.TopDualAdditive
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# U-pairs

For a dual-closed full additive subcategory `𝒰 ⊂ 𝒜`, let `i = Kar(incl) : Kar 𝒰 → Kar 𝒜` be the
completion of the inclusion, a strict duality functor. A *strict `k`-dimensional `𝒰`-pair* over
`(P, π)` consists of a strict `(k-1)`-dimensional symmetric Poincaré complex `(P, π)` in `Kar 𝒰`
and a strict `k`-dimensional Poincaré pair `(f : i P ⟶ D, δφ, i_% π)` in `Kar 𝒜`.

Lean: the boundary condition is an equation of structured complexes
`(V.C, V.φ) = (i P, i_% π)`, as in `HSP.Cobordant`. The zero `𝒰`-pair shows the notion is not
vacuous, for every `𝒰 ⊂ 𝒜` and `k`; the named witness at an explicit toy instance is the zero
`0`-dimensional `𝒰`-pair for based ℚ-vector spaces (`HSP.FreeQ`) with `𝒰` all objects.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

open scoped ZeroObject

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- **U-pairs.** A strict `k`-dimensional `𝒰`-pair: a strict `(k-1)`-dimensional symmetric
Poincaré complex `(P, π)` in `Kar 𝒰` and a strict `k`-dimensional Poincaré pair in `Kar 𝒜` with
boundary `(i P, i_% π)`. -/
structure UPair (U : ObjectProperty A) [IsDualAdditive U] (k : ℤ) where
  /-- The complex `(P, π)` over `Kar 𝒰`. -/
  P : SymPoincare (Karoubi U.FullSubcategory) (k - 1)
  /-- The pair `(f : i P ⟶ D, δφ, i_% π)` in `Kar 𝒜`. -/
  V : SymPair (Karoubi A) (k - 1) k
  /-- The boundary of the pair is `(i P, i_% π)`. -/
  boundary_eq : (⟨V.C, V.φ⟩ : Σ C : ChainComplex (Karoubi A) ℤ, (StructureCx C).X (k - 1)) =
    ⟨(DualSubcategory.incl U).kar.mapCx P.C,
      (DualSubcategory.incl U).kar.mapStructure P.C (k - 1) P.φ⟩

/-! Non-vacuity: the zero `𝒰`-pair, all of whose chain objects are zero objects. -/

section NonVacuity

variable {B : Type*} [Category B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

omit [Linear ℚ B] [HasFiniteBiproducts B] [DualCat B] in
private lemma exists_homotopyEquiv_of_isZero {K L : ChainComplex B ℤ}
    (hK : ∀ r, IsZero (K.X r)) (hL : ∀ r, IsZero (L.X r)) (g : K ⟶ L) :
    ∃ e : HomotopyEquiv K L, e.hom = g :=
  ⟨HomotopyEquiv.ofIso (HomologicalComplex.Hom.isoOfComponents (fun r => (hK r).iso (hL r))
    fun i _ _ => (hK i).eq_of_src _ _), by ext r; exact (hK r).eq_of_src _ _⟩

private lemma isZero_dual {X : B} (hX : IsZero X) : IsZero (dual X) := by
  rw [IsZero.iff_id_eq_zero, ← dualHom_id, (IsZero.iff_id_eq_zero X).mp hX, dualHom_zero]

omit [Linear ℚ B] [DualCat B] in
private lemma isZero_biprod {X Y : B} (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⊞ Y) := by
  rw [IsZero.iff_id_eq_zero, ← biprod.total, hX.eq_of_tgt biprod.fst 0,
    hY.eq_of_tgt biprod.snd 0, zero_comp, zero_comp, add_zero]

/-- The complex of zero objects. -/
private noncomputable def zeroCx : ChainComplex B ℤ where
  X _ := 0
  d _ _ := 0

omit [Linear ℚ B] [DualCat B] in
private lemma isZero_zeroCx (r : ℤ) : IsZero ((zeroCx : ChainComplex B ℤ).X r) := isZero_zero _

/-- The zero complex with the zero structure. -/
private noncomputable def zeroPoincare (k : ℤ) : SymPoincare B k where
  C := zeroCx
  φ := 0
  bounded r _ := isZero_zeroCx r
  cycle := map_zero _
  symmetric := map_zero _
  poincare := exists_homotopyEquiv_of_isZero (fun _ => isZero_dual (isZero_zeroCx _))
    isZero_zeroCx _

/-- The pair `(1 : C ⟶ C, 0, 0)` for a complex `C` of zero objects. -/
private noncomputable def zeroPair {m n : ℤ} (hmn : m + 1 = n) (C : ChainComplex B ℤ)
    (hC : ∀ r, IsZero (C.X r)) : SymPair B m n where
  C := C
  D := C
  f := 𝟙 C
  δφ := 0
  φ := 0
  dim := hmn
  boundary_bounded r _ := hC r
  boundary_cycle := map_zero _
  boundary_symmetric := map_zero _
  boundary_poincare :=
    exists_homotopyEquiv_of_isZero (fun _ => isZero_dual (hC _)) hC _
  bounded r _ := hC r
  symmetric := map_zero _
  rel := by rw [map_zero, map_zero]
  poincare := exists_homotopyEquiv_of_isZero (fun _ => isZero_dual (hC _))
    (fun r => isZero_biprod (hC r) (hC (r - 1))) _

end NonVacuity

/-- The zero `𝒰`-pair: `(P, π) = (0, 0)` in `Kar 𝒰` and the pair `(1 : i 0 ⟶ i 0, 0, 0)`. -/
private noncomputable def zeroUPair (U : ObjectProperty A) [IsDualAdditive U] (k : ℤ) :
    UPair U k :=
  have hC : ∀ r, IsZero (((DualSubcategory.incl U).kar.mapCx
      (zeroPoincare (B := Karoubi U.FullSubcategory) (k - 1)).C).X r) := fun r =>
    Functor.map_isZero (DualSubcategory.incl U).kar.toFunctor
      (isZero_zeroCx (B := Karoubi U.FullSubcategory) r)
  { P := zeroPoincare (k - 1)
    V := zeroPair (by ring) _ hC
    boundary_eq := by
      change (⟨_, 0⟩ : Σ C : ChainComplex (Karoubi A) ℤ, (StructureCx C).X (k - 1)) = ⟨_, _⟩
      congr 1
      exact (map_zero _).symm }

private theorem uPair_nonempty (U : ObjectProperty A) [IsDualAdditive U] (k : ℤ) :
    Nonempty (UPair U k) :=
  ⟨zeroUPair U k⟩

/-- Non-vacuity at an explicit toy instance: `𝒜 = ℚ` (based ℚ-vector spaces, `HSP.FreeQ`, with
`(ℚ^d)^* = ℚ^d`, `g^* = gᵀ`), `𝒰 = 𝒜` (every object), and the zero `0`-dimensional `𝒰`-pair. -/
private noncomputable def uPairFreeQ : UPair (⊤ : ObjectProperty FreeQ) 0 :=
  zeroUPair ⊤ 0

end HSP
